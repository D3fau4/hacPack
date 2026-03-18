#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <time.h>
#include "nca.h"
#include "sha.h"
#include "filepath.h"
#include "romfs.h"
#include "cnmt.h"
#include "ticket.h"
#include "rsa.h"

#define NCA_PATCH_BLOCK_SIZE 0x10
#define NCA_PATCH_SAME_OFFSET_REUSE_MIN_SIZE 0x20
#define NCA_PATCH_RELOCATED_REUSE_MIN_SIZE 0x40
#define NCA_PATCH_LOCAL_SEARCH_WINDOW 0x1000
#define NCA_PATCH_GOOD_MATCH_SIZE 0x4000
#define NCA_PATCH_COMPARE_BUFFER_SIZE 0x4000
#define NCA_PATCH_SOFT_SEGMENT_LIMIT (BKTR_RELOCATION_ENTRY_CAPACITY * 4)
#define NCA_PATCH_GLOBAL_INDEX_MAX_BYTES (64U * 1024U * 1024U)
#define NCA_PATCH_GLOBAL_INDEX_MAX_PROBES 8
#define NCA_PATCH_GLOBAL_INDEX_CANDIDATES 8
#define NCA_PATCH_FILE_HINT_SAMPLE_SIZE 0x100
#define NCA_PATCH_INDEX_READ_CHUNK (4U * 1024U * 1024U)
#define NCA_PATCH_SKIP_SEARCH_THRESHOLD_SMALL 0x40000
#define NCA_PATCH_SKIP_SEARCH_THRESHOLD_MEDIUM 0x200000
#define NCA_PATCH_SKIP_SEARCH_THRESHOLD_LARGE 0x1000000
#define NCA_PATCH_SKIP_SEARCH_STEP_SMALL 0x400
#define NCA_PATCH_SKIP_SEARCH_STEP_MEDIUM 0x4000
#define NCA_PATCH_SKIP_SEARCH_STEP_LARGE 0x10000

typedef struct
{
    bktr_relocation_segment_t *segments;
    uint32_t segment_count;
    uint64_t patch_data_size;
} nca_patch_layout_t;

typedef struct
{
    uint64_t virtual_offset;
    uint64_t base_offset;
    uint64_t size;
} nca_base_match_t;

typedef struct
{
    uint64_t current_offset;
    uint64_t base_offset;
    uint64_t size;
} nca_patch_hint_t;

typedef struct
{
    uint64_t fingerprint;
    uint32_t candidate_count;
    uint32_t seen_count;
    uint64_t base_offsets[NCA_PATCH_GLOBAL_INDEX_CANDIDATES];
} nca_base_block_index_entry_t;

typedef struct
{
    nca_base_block_index_entry_t *entries;
    uint32_t slot_count;
} nca_base_block_index_t;

typedef struct
{
    FILE *file;
    unsigned char *buffer;
    uint64_t file_size;
    uint64_t window_offset;
    size_t window_size;
    size_t capacity;
} nca_cached_reader_t;

typedef struct
{
    FILE *file;
    unsigned char *chunk;
    uint64_t *fingerprints;
    uint64_t file_size;
    uint64_t chunk_offset;
    size_t chunk_size;
    size_t loaded_size;
} nca_current_block_cache_t;

typedef struct
{
    uint64_t hash;
    uint32_t index;
    const char *path;
} nca_path_hash_entry_t;

typedef struct
{
    nca_path_hash_entry_t *entries;
    uint32_t slot_count;
} nca_path_hash_table_t;

typedef struct
{
    uint64_t hash;
    uint64_t size;
    uint64_t signature;
    uint32_t count;
    uint32_t index;
} nca_signature_hash_entry_t;

typedef struct
{
    nca_signature_hash_entry_t *entries;
    uint32_t slot_count;
} nca_signature_hash_table_t;

static uint32_t nca_next_power_of_two_u32(uint32_t value);
static uint64_t nca_measure_base_match(nca_cached_reader_t *base_reader, uint64_t base_size, uint64_t base_offset, nca_cached_reader_t *current_reader, uint64_t current_size, uint64_t current_offset);
static uint64_t nca_measure_base_match_backwards(nca_cached_reader_t *base_reader, uint64_t base_offset, nca_cached_reader_t *current_reader, uint64_t current_offset, uint64_t max_backtrack_size);
static int nca_try_read_file_exact(FILE *file, uint64_t offset, void *buffer, size_t size);
static int nca_compare_patch_hints(const void *left, const void *right);
static void nca_merge_patch_hints(nca_patch_hint_t *hints, uint32_t *hint_count);
static const nca_patch_hint_t *nca_find_patch_hint(const nca_patch_hint_t *hints, uint32_t hint_count, uint64_t current_offset);
static uint64_t nca_hash_bytes(const unsigned char *data, size_t size, uint64_t seed);
static uint64_t nca_hash_block(const unsigned char *block);
static uint64_t nca_compute_file_hint_signature(const filepath_t *source_path, uint64_t size);
static uint64_t nca_choose_patch_probe_step(uint64_t pending_patch_size);
static void nca_profile_add(double *total_ms, uint64_t start_ticks);

static uint64_t nca_get_file_size(FILE *file)
{
    uint64_t current_offset = ftello64(file);
    fseeko64(file, 0, SEEK_END);
    uint64_t size = (uint64_t)ftello64(file);
    fseeko64(file, current_offset, SEEK_SET);
    return size;
}

static uint32_t nca_get_section_generation(const nca_fs_header_t *fs_header)
{
    const uint8_t *b = (const uint8_t *)fs_header->section_ctr + 4;
    return ((uint32_t)b[0] << 24) | ((uint32_t)b[1] << 16) |
           ((uint32_t)b[2] << 8)  |  (uint32_t)b[3];
}

static uint64_t nca_profile_now_ticks(void)
{
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return ((uint64_t)ts.tv_sec * 1000000000ULL) + (uint64_t)ts.tv_nsec;
}

static void nca_profile_add(double *total_ms, uint64_t start_ticks)
{
    uint64_t elapsed = nca_profile_now_ticks() - start_ticks;
    *total_ms += (double)elapsed / 1000000.0;
}

static uint64_t nca_hash_string(const char *value)
{
    static const uint64_t fnv_offset_basis = 0xCBF29CE484222325ULL;
    return nca_hash_bytes((const unsigned char *)value, strlen(value), fnv_offset_basis);
}

static void nca_cached_reader_init(nca_cached_reader_t *reader, FILE *file, uint64_t file_size, size_t capacity)
{
    memset(reader, 0, sizeof(*reader));
    reader->file = file;
    reader->file_size = file_size;
    reader->capacity = capacity;
    if (file == NULL || capacity == 0)
    {
        return;
    }

    reader->buffer = malloc(capacity);
    if (reader->buffer == NULL)
    {
        FATAL_ERROR("Failed to allocate cached reader buffer");
    }
}

static void nca_cached_reader_free(nca_cached_reader_t *reader)
{
    free(reader->buffer);
    memset(reader, 0, sizeof(*reader));
}

static int nca_cached_reader_try_read(nca_cached_reader_t *reader, uint64_t offset, void *buffer, size_t size)
{
    if (size == 0)
    {
        return 1;
    }
    if (reader->file == NULL || offset + size > reader->file_size)
    {
        return 0;
    }
    if (size > reader->capacity)
    {
        return nca_try_read_file_exact(reader->file, offset, buffer, size);
    }

    if (reader->window_size == 0 ||
        offset < reader->window_offset ||
        offset + size > reader->window_offset + reader->window_size)
    {
        uint64_t window_offset = offset - (offset % reader->capacity);
        if (window_offset + reader->capacity < offset + size)
        {
            window_offset = offset;
        }
        if (window_offset + reader->capacity > reader->file_size && reader->file_size > reader->capacity)
        {
            window_offset = reader->file_size - reader->capacity;
        }

        reader->window_offset = window_offset;
        reader->window_size = (size_t)(reader->file_size - window_offset);
        if (reader->window_size > reader->capacity)
        {
            reader->window_size = reader->capacity;
        }

        if (!nca_try_read_file_exact(reader->file, reader->window_offset, reader->buffer, reader->window_size))
        {
            reader->window_size = 0;
            return 0;
        }
    }

    memcpy(buffer, reader->buffer + (offset - reader->window_offset), size);
    return 1;
}

static void nca_current_block_cache_init(nca_current_block_cache_t *cache, FILE *file, uint64_t file_size, size_t chunk_size)
{
    memset(cache, 0, sizeof(*cache));
    cache->file = file;
    cache->file_size = file_size;
    cache->chunk_size = chunk_size;
    if (file == NULL || chunk_size == 0)
    {
        return;
    }

    cache->chunk = malloc(chunk_size);
    cache->fingerprints = malloc((chunk_size / NCA_PATCH_BLOCK_SIZE) * sizeof(*cache->fingerprints));
    if (cache->chunk == NULL || cache->fingerprints == NULL)
    {
        free(cache->chunk);
        free(cache->fingerprints);
        FATAL_ERROR("Failed to allocate current block cache");
    }
}

static void nca_current_block_cache_free(nca_current_block_cache_t *cache)
{
    free(cache->chunk);
    free(cache->fingerprints);
    memset(cache, 0, sizeof(*cache));
}

static void nca_current_block_cache_load(nca_current_block_cache_t *cache, uint64_t offset)
{
    uint64_t chunk_offset = offset - (offset % cache->chunk_size);
    size_t to_read;

    if (cache->loaded_size > 0 &&
        offset >= cache->chunk_offset &&
        offset + NCA_PATCH_BLOCK_SIZE <= cache->chunk_offset + cache->loaded_size)
    {
        return;
    }

    cache->chunk_offset = chunk_offset;
    to_read = (size_t)(cache->file_size - chunk_offset);
    if (to_read > cache->chunk_size)
    {
        to_read = cache->chunk_size;
    }
    to_read -= to_read % NCA_PATCH_BLOCK_SIZE;
    cache->loaded_size = to_read;

    if (to_read == 0)
    {
        return;
    }
    if (!nca_try_read_file_exact(cache->file, cache->chunk_offset, cache->chunk, to_read))
    {
        FATAL_ERROR("Failed to read current RomFS section");
    }

    for (size_t i = 0; i < to_read; i += NCA_PATCH_BLOCK_SIZE)
    {
        cache->fingerprints[i / NCA_PATCH_BLOCK_SIZE] = nca_hash_block(cache->chunk + i);
    }
}

static const unsigned char *nca_current_block_cache_get_block(nca_current_block_cache_t *cache, uint64_t offset, uint64_t *out_fingerprint)
{
    nca_current_block_cache_load(cache, offset);
    if (cache->loaded_size == 0 || offset + NCA_PATCH_BLOCK_SIZE > cache->chunk_offset + cache->loaded_size)
    {
        return NULL;
    }

    size_t block_index = (size_t)((offset - cache->chunk_offset) / NCA_PATCH_BLOCK_SIZE);
    *out_fingerprint = cache->fingerprints[block_index];
    return cache->chunk + (block_index * NCA_PATCH_BLOCK_SIZE);
}

static void nca_path_hash_table_init(nca_path_hash_table_t *table, uint32_t count)
{
    memset(table, 0, sizeof(*table));
    if (count == 0)
    {
        return;
    }

    table->slot_count = nca_next_power_of_two_u32(count * 2);
    table->entries = calloc(table->slot_count, sizeof(*table->entries));
    if (table->entries == NULL)
    {
        FATAL_ERROR("Failed to allocate path hash table");
    }
}

static void nca_path_hash_table_free(nca_path_hash_table_t *table)
{
    free(table->entries);
    memset(table, 0, sizeof(*table));
}

static void nca_path_hash_table_insert(nca_path_hash_table_t *table, const char *path, uint32_t index)
{
    uint64_t hash = nca_hash_string(path);
    uint32_t mask = table->slot_count - 1;
    uint32_t slot = (uint32_t)hash & mask;

    for (uint32_t probe = 0; probe < table->slot_count; probe++)
    {
        nca_path_hash_entry_t *entry = &table->entries[(slot + probe) & mask];
        if (entry->path == NULL)
        {
            entry->hash = hash;
            entry->index = index;
            entry->path = path;
            return;
        }
    }

    FATAL_ERROR("Path hash table is full");
}

static int nca_path_hash_table_find(const nca_path_hash_table_t *table, const char *path, uint32_t *out_index)
{
    uint64_t hash = nca_hash_string(path);
    uint32_t mask;
    uint32_t slot;

    if (table->entries == NULL || table->slot_count == 0)
    {
        return 0;
    }

    mask = table->slot_count - 1;
    slot = (uint32_t)hash & mask;
    for (uint32_t probe = 0; probe < table->slot_count; probe++)
    {
        const nca_path_hash_entry_t *entry = &table->entries[(slot + probe) & mask];
        if (entry->path == NULL)
        {
            return 0;
        }
        if (entry->hash == hash && strcmp(entry->path, path) == 0)
        {
            *out_index = entry->index;
            return 1;
        }
    }

    return 0;
}

static void nca_signature_hash_table_init(nca_signature_hash_table_t *table, uint32_t count)
{
    memset(table, 0, sizeof(*table));
    if (count == 0)
    {
        return;
    }

    table->slot_count = nca_next_power_of_two_u32(count * 2);
    table->entries = calloc(table->slot_count, sizeof(*table->entries));
    if (table->entries == NULL)
    {
        FATAL_ERROR("Failed to allocate signature hash table");
    }
}

static void nca_signature_hash_table_free(nca_signature_hash_table_t *table)
{
    free(table->entries);
    memset(table, 0, sizeof(*table));
}

static void nca_signature_hash_table_insert(nca_signature_hash_table_t *table, uint64_t size, uint64_t signature, uint32_t index)
{
    uint64_t hash = nca_hash_bytes((const unsigned char *)&size, sizeof(size), signature);
    uint32_t mask = table->slot_count - 1;
    uint32_t slot = (uint32_t)hash & mask;

    for (uint32_t probe = 0; probe < table->slot_count; probe++)
    {
        nca_signature_hash_entry_t *entry = &table->entries[(slot + probe) & mask];
        if (entry->count == 0)
        {
            entry->hash = hash;
            entry->size = size;
            entry->signature = signature;
            entry->count = 1;
            entry->index = index;
            return;
        }
        if (entry->hash == hash && entry->size == size && entry->signature == signature)
        {
            entry->count++;
            return;
        }
    }

    FATAL_ERROR("Signature hash table is full");
}

static const nca_signature_hash_entry_t *nca_signature_hash_table_find(const nca_signature_hash_table_t *table, uint64_t size, uint64_t signature)
{
    uint64_t hash = nca_hash_bytes((const unsigned char *)&size, sizeof(size), signature);
    uint32_t mask;
    uint32_t slot;

    if (table->entries == NULL || table->slot_count == 0)
    {
        return NULL;
    }

    mask = table->slot_count - 1;
    slot = (uint32_t)hash & mask;
    for (uint32_t probe = 0; probe < table->slot_count; probe++)
    {
        const nca_signature_hash_entry_t *entry = &table->entries[(slot + probe) & mask];
        if (entry->count == 0)
        {
            return NULL;
        }
        if (entry->hash == hash && entry->size == size && entry->signature == signature)
        {
            return entry;
        }
    }

    return NULL;
}

static int nca_compare_patch_hints(const void *left, const void *right)
{
    const nca_patch_hint_t *left_hint = left;
    const nca_patch_hint_t *right_hint = right;

    if (left_hint->current_offset < right_hint->current_offset)
    {
        return -1;
    }
    if (left_hint->current_offset > right_hint->current_offset)
    {
        return 1;
    }
    return 0;
}

static void nca_merge_patch_hints(nca_patch_hint_t *hints, uint32_t *hint_count)
{
    uint32_t out_index = 0;

    for (uint32_t i = 0; i < *hint_count; i++)
    {
        if (hints[i].size == 0)
        {
            continue;
        }

        if (out_index > 0)
        {
            nca_patch_hint_t *previous = &hints[out_index - 1];
            if (previous->current_offset + previous->size == hints[i].current_offset &&
                previous->base_offset + previous->size == hints[i].base_offset)
            {
                previous->size += hints[i].size;
                continue;
            }
        }

        hints[out_index++] = hints[i];
    }

    *hint_count = out_index;
}

static const nca_patch_hint_t *nca_find_patch_hint(const nca_patch_hint_t *hints, uint32_t hint_count, uint64_t current_offset)
{
    uint32_t left = 0;
    uint32_t right = hint_count;

    while (left < right)
    {
        uint32_t middle = left + ((right - left) / 2);
        if (hints[middle].current_offset <= current_offset)
        {
            left = middle + 1;
        }
        else
        {
            right = middle;
        }
    }

    if (left == 0)
    {
        return NULL;
    }

    const nca_patch_hint_t *hint = &hints[left - 1];
    if (current_offset < hint->current_offset + hint->size)
    {
        return hint;
    }

    return NULL;
}

static uint64_t nca_hash_bytes(const unsigned char *data, size_t size, uint64_t seed)
{
    uint64_t hash = seed;

    for (size_t i = 0; i < size; i++)
    {
        hash ^= data[i];
        hash *= 0x100000001B3ULL;
        hash ^= hash >> 32;
    }

    return hash;
}

static uint64_t nca_compute_file_hint_signature(const filepath_t *source_path, uint64_t size)
{
    static const uint64_t fnv_offset_basis = 0xCBF29CE484222325ULL;
    unsigned char buffer[NCA_PATCH_FILE_HINT_SAMPLE_SIZE];
    uint64_t hash = fnv_offset_basis;
    FILE *file = os_fopen(source_path->os_path, OS_MODE_READ);
    uint64_t sample_offsets[3];
    uint32_t sample_count = 0;

    if (file == NULL)
    {
        fprintf(stderr, "Failed to open %s!\n", source_path->char_path);
        exit(EXIT_FAILURE);
    }

    hash = nca_hash_bytes((const unsigned char *)&size, sizeof(size), hash);
    sample_offsets[sample_count++] = 0;

    if (size > NCA_PATCH_FILE_HINT_SAMPLE_SIZE)
    {
        uint64_t middle = 0;
        uint64_t end = size - NCA_PATCH_FILE_HINT_SAMPLE_SIZE;

        if (size > (NCA_PATCH_FILE_HINT_SAMPLE_SIZE * 2))
        {
            middle = (size / 2) - (NCA_PATCH_FILE_HINT_SAMPLE_SIZE / 2);
        }

        if (middle > 0 && middle != sample_offsets[0] && middle != end)
        {
            sample_offsets[sample_count++] = middle;
        }
        if (end != sample_offsets[0] && (sample_count < 2 || end != sample_offsets[1]))
        {
            sample_offsets[sample_count++] = end;
        }
    }

    for (uint32_t i = 0; i < sample_count; i++)
    {
        uint64_t read_size = size - sample_offsets[i];
        if (read_size > sizeof(buffer))
        {
            read_size = sizeof(buffer);
        }

        if (!nca_try_read_file_exact(file, sample_offsets[i], buffer, (size_t)read_size))
        {
            fclose(file);
            fprintf(stderr, "Failed to read %s!\n", source_path->char_path);
            exit(EXIT_FAILURE);
        }

        hash = nca_hash_bytes((const unsigned char *)&sample_offsets[i], sizeof(sample_offsets[i]), hash);
        hash = nca_hash_bytes(buffer, (size_t)read_size, hash);
    }

    fclose(file);
    return hash;
}

static uint64_t nca_hash_block(const unsigned char *block)
{
    uint64_t part0 = 0;
    uint64_t part1 = 0;

    memcpy(&part0, block, sizeof(part0));
    memcpy(&part1, block + sizeof(part0), sizeof(part1));

    part0 ^= part1 + 0x9E3779B97F4A7C15ULL + (part0 << 6) + (part0 >> 2);
    part0 ^= part0 >> 30;
    part0 *= 0xBF58476D1CE4E5B9ULL;
    part0 ^= part0 >> 27;
    part0 *= 0x94D049BB133111EBULL;
    part0 ^= part0 >> 31;

    if (part0 == 0)
    {
        part0 = 1;
    }

    return part0;
}

static uint32_t nca_next_power_of_two_u32(uint32_t value)
{
    if (value <= 1)
    {
        return 1;
    }

    value--;
    value |= value >> 1;
    value |= value >> 2;
    value |= value >> 4;
    value |= value >> 8;
    value |= value >> 16;
    return value + 1;
}

static void nca_base_block_index_init(nca_base_block_index_t *index)
{
    memset(index, 0, sizeof(*index));
}

static void nca_base_block_index_free(nca_base_block_index_t *index)
{
    free(index->entries);
    memset(index, 0, sizeof(*index));
}

static void nca_base_block_index_insert(nca_base_block_index_t *index, uint64_t fingerprint, uint64_t base_offset)
{
    uint32_t mask = index->slot_count - 1;
    uint32_t slot = (uint32_t)fingerprint & mask;

    for (uint32_t probe = 0; probe < NCA_PATCH_GLOBAL_INDEX_MAX_PROBES; probe++)
    {
        nca_base_block_index_entry_t *entry = &index->entries[(slot + probe) & mask];
        if (entry->fingerprint == 0 || entry->fingerprint == fingerprint)
        {
            if (entry->fingerprint == 0)
            {
                memset(entry, 0, sizeof(*entry));
                entry->fingerprint = fingerprint;
            }

            entry->fingerprint = fingerprint;
            if (entry->candidate_count < NCA_PATCH_GLOBAL_INDEX_CANDIDATES)
            {
                entry->base_offsets[entry->candidate_count++] = base_offset;
            }
            else
            {
                entry->base_offsets[entry->seen_count % NCA_PATCH_GLOBAL_INDEX_CANDIDATES] = base_offset;
            }
            entry->seen_count++;
            return;
        }
    }

    memset(&index->entries[slot], 0, sizeof(index->entries[slot]));
    index->entries[slot].fingerprint = fingerprint;
    index->entries[slot].base_offsets[0] = base_offset;
    index->entries[slot].candidate_count = 1;
    index->entries[slot].seen_count = 1;
}

static void nca_build_base_block_index(FILE *base_file, uint64_t base_size, nca_base_block_index_t *index)
{
    uint64_t base_offset = 0;
    uint64_t block_count = base_size / NCA_PATCH_BLOCK_SIZE;
    uint64_t max_slots = NCA_PATCH_GLOBAL_INDEX_MAX_BYTES / sizeof(nca_base_block_index_entry_t);
    uint32_t slot_count;

    nca_base_block_index_init(index);

    if (block_count == 0 || max_slots < 2)
    {
        return;
    }

    if (block_count * 2 < max_slots)
    {
        max_slots = block_count * 2;
    }

    slot_count = nca_next_power_of_two_u32((uint32_t)max_slots);
    index->entries = calloc(slot_count, sizeof(*index->entries));
    if (index->entries == NULL)
    {
        FATAL_ERROR("Failed to allocate global base block index");
    }
    index->slot_count = slot_count;

    unsigned char *chunk = malloc(NCA_PATCH_INDEX_READ_CHUNK);
    if (chunk == NULL)
    {
        FATAL_ERROR("Failed to allocate base block index read buffer");
    }

    fseeko64(base_file, 0, SEEK_SET);
    while (base_offset + NCA_PATCH_BLOCK_SIZE <= base_size)
    {
        size_t to_read = NCA_PATCH_INDEX_READ_CHUNK;
        if (base_offset + to_read > base_size)
        {
            to_read = (size_t)(base_size - base_offset);
        }
        to_read -= to_read % NCA_PATCH_BLOCK_SIZE;

        if (fread(chunk, 1, to_read, base_file) != to_read)
        {
            FATAL_ERROR("Failed to read base RomFS section");
        }

        for (size_t i = 0; i < to_read; i += NCA_PATCH_BLOCK_SIZE)
        {
            nca_base_block_index_insert(index, nca_hash_block(chunk + i), base_offset);
            base_offset += NCA_PATCH_BLOCK_SIZE;
        }
    }

    free(chunk);
}

static uint64_t nca_find_indexed_base_match(const nca_base_block_index_t *index, nca_cached_reader_t *base_reader, uint64_t base_size, uint64_t current_block_fingerprint, nca_cached_reader_t *current_reader, uint64_t current_size, uint64_t current_offset, uint64_t *out_base_offset)
{
    uint32_t mask;
    uint32_t slot;
    uint64_t best_offset = 0;
    uint64_t best_size = 0;

    if (index->entries == NULL || index->slot_count == 0)
    {
        return 0;
    }

    mask = index->slot_count - 1;
    slot = (uint32_t)current_block_fingerprint & mask;

    for (uint32_t probe = 0; probe < NCA_PATCH_GLOBAL_INDEX_MAX_PROBES; probe++)
    {
        nca_base_block_index_entry_t *entry = &index->entries[(slot + probe) & mask];

        if (entry->fingerprint == 0)
        {
            break;
        }
        if (entry->fingerprint != current_block_fingerprint)
        {
            continue;
        }

        for (uint32_t candidate_index = 0; candidate_index < entry->candidate_count; candidate_index++)
        {
            uint64_t candidate_offset = entry->base_offsets[candidate_index];
            uint64_t candidate_size = nca_measure_base_match(base_reader, base_size, candidate_offset, current_reader, current_size, current_offset);

            if (candidate_size >= NCA_PATCH_RELOCATED_REUSE_MIN_SIZE && candidate_size > best_size)
            {
                best_offset = candidate_offset;
                best_size = candidate_size;
            }
            if (best_size >= NCA_PATCH_GOOD_MATCH_SIZE)
            {
                break;
            }
        }

        if (best_size >= NCA_PATCH_GOOD_MATCH_SIZE)
        {
            break;
        }
    }

    if (best_size > 0)
    {
        *out_base_offset = best_offset;
    }
    return best_size;
}

static void nca_append_layout_segment(nca_patch_layout_t *layout, uint32_t *capacity, uint64_t virtual_offset, uint64_t size, uint64_t physical_offset, uint32_t is_patch)
{
    if (size == 0)
    {
        return;
    }

    if (layout->segment_count > 0)
    {
        bktr_relocation_segment_t *last_segment = &layout->segments[layout->segment_count - 1];
        if (last_segment->is_patch == is_patch &&
            last_segment->virtual_offset + last_segment->size == virtual_offset &&
            (is_patch || last_segment->physical_offset + last_segment->size == physical_offset))
        {
            last_segment->size += size;
            if (is_patch)
            {
                layout->patch_data_size += size;
            }
            return;
        }
    }

    if (layout->segment_count == *capacity)
    {
        uint32_t new_capacity = (*capacity == 0) ? 16 : (*capacity * 2);
        bktr_relocation_segment_t *new_segments = realloc(layout->segments, sizeof(*layout->segments) * new_capacity);
        if (new_segments == NULL)
        {
            FATAL_ERROR("Failed to allocate BKTR relocation segments");
        }
        layout->segments = new_segments;
        *capacity = new_capacity;
    }

    layout->segments[layout->segment_count].virtual_offset = virtual_offset;
    layout->segments[layout->segment_count].size = size;
    layout->segments[layout->segment_count].physical_offset = physical_offset;
    layout->segments[layout->segment_count].is_patch = is_patch;

    if (is_patch)
    {
        layout->patch_data_size += size;
    }

    layout->segment_count++;
}

static void nca_append_patch_data_segment(nca_patch_layout_t *layout, uint32_t *capacity, uint64_t virtual_offset, uint64_t size)
{
    nca_append_layout_segment(layout, capacity, virtual_offset, size, layout->patch_data_size, 1);
}

static void nca_append_base_segment(nca_patch_layout_t *layout, uint32_t *capacity, uint64_t virtual_offset, uint64_t size, uint64_t base_offset)
{
    nca_append_layout_segment(layout, capacity, virtual_offset, size, base_offset, 0);
}

static void nca_finalize_patch_layout(nca_patch_layout_t *layout)
{
    uint32_t out_index = 0;
    uint64_t patch_data_size = 0;

    for (uint32_t i = 0; i < layout->segment_count; i++)
    {
        bktr_relocation_segment_t segment = layout->segments[i];
        if (segment.size == 0)
        {
            continue;
        }

        if (segment.is_patch)
        {
            segment.physical_offset = patch_data_size;
            patch_data_size += segment.size;
        }

        if (out_index > 0)
        {
            bktr_relocation_segment_t *previous = &layout->segments[out_index - 1];
            if (previous->is_patch == segment.is_patch &&
                previous->virtual_offset + previous->size == segment.virtual_offset &&
                (segment.is_patch || previous->physical_offset + previous->size == segment.physical_offset))
            {
                previous->size += segment.size;
                continue;
            }
        }

        layout->segments[out_index++] = segment;
    }

    layout->segment_count = out_index;
    layout->patch_data_size = patch_data_size;
}

static void nca_absorb_small_base_segments(nca_patch_layout_t *layout, uint64_t max_size)
{
    for (uint32_t i = 0; i < layout->segment_count; i++)
    {
        if (layout->segments[i].is_patch != 0 || layout->segments[i].size > max_size)
        {
            continue;
        }

        if ((i > 0 && layout->segments[i - 1].is_patch != 0) ||
            (i + 1 < layout->segment_count && layout->segments[i + 1].is_patch != 0))
        {
            layout->segments[i].is_patch = 1;
        }
    }

    nca_finalize_patch_layout(layout);
}

static void nca_build_full_patch_layout(nca_patch_layout_t *layout, uint64_t size)
{
    uint32_t capacity = 0;

    free(layout->segments);
    memset(layout, 0, sizeof(*layout));
    nca_append_patch_data_segment(layout, &capacity, 0, size);
}

static uint64_t nca_choose_patch_probe_step(uint64_t pending_patch_size)
{
    if (pending_patch_size >= NCA_PATCH_SKIP_SEARCH_THRESHOLD_LARGE)
    {
        return NCA_PATCH_SKIP_SEARCH_STEP_LARGE;
    }
    if (pending_patch_size >= NCA_PATCH_SKIP_SEARCH_THRESHOLD_MEDIUM)
    {
        return NCA_PATCH_SKIP_SEARCH_STEP_MEDIUM;
    }
    if (pending_patch_size >= NCA_PATCH_SKIP_SEARCH_THRESHOLD_SMALL)
    {
        return NCA_PATCH_SKIP_SEARCH_STEP_SMALL;
    }
    return NCA_PATCH_BLOCK_SIZE;
}

static int nca_try_read_file_exact(FILE *file, uint64_t offset, void *buffer, size_t size)
{
    if (fseeko64(file, offset, SEEK_SET) != 0)
    {
        return 0;
    }

    return fread(buffer, 1, size, file) == size;
}

static uint64_t nca_measure_base_match(nca_cached_reader_t *base_reader, uint64_t base_size, uint64_t base_offset, nca_cached_reader_t *current_reader, uint64_t current_size, uint64_t current_offset)
{
    unsigned char base_buffer[NCA_PATCH_COMPARE_BUFFER_SIZE];
    unsigned char current_buffer[NCA_PATCH_COMPARE_BUFFER_SIZE];
    uint64_t remaining_size = base_size - base_offset;
    uint64_t current_remaining_size = current_size - current_offset;
    uint64_t matched_size = 0;

    if (current_remaining_size < remaining_size)
    {
        remaining_size = current_remaining_size;
    }

    remaining_size -= (remaining_size % NCA_PATCH_BLOCK_SIZE);
    while (remaining_size > 0)
    {
        uint64_t read_size = remaining_size;
        if (read_size > sizeof(base_buffer))
        {
            read_size = sizeof(base_buffer);
        }
        read_size -= (read_size % NCA_PATCH_BLOCK_SIZE);

        if (!nca_cached_reader_try_read(base_reader, base_offset + matched_size, base_buffer, (size_t)read_size) ||
            !nca_cached_reader_try_read(current_reader, current_offset + matched_size, current_buffer, (size_t)read_size))
        {
            return 0;
        }

        if (memcmp(base_buffer, current_buffer, (size_t)read_size) == 0)
        {
            matched_size += read_size;
            remaining_size -= read_size;
            continue;
        }

        for (uint64_t i = 0; i < read_size; i += NCA_PATCH_BLOCK_SIZE)
        {
            if (memcmp(base_buffer + i, current_buffer + i, NCA_PATCH_BLOCK_SIZE) != 0)
            {
                return matched_size + i;
            }
        }

        matched_size += read_size;
        remaining_size -= read_size;
    }

    return matched_size;
}

static uint64_t nca_measure_base_match_backwards(nca_cached_reader_t *base_reader, uint64_t base_offset, nca_cached_reader_t *current_reader, uint64_t current_offset, uint64_t max_backtrack_size)
{
    unsigned char base_buffer[NCA_PATCH_COMPARE_BUFFER_SIZE];
    unsigned char current_buffer[NCA_PATCH_COMPARE_BUFFER_SIZE];
    uint64_t matched_size = 0;

    if (base_offset < max_backtrack_size)
    {
        max_backtrack_size = base_offset;
    }
    if (current_offset < max_backtrack_size)
    {
        max_backtrack_size = current_offset;
    }

    max_backtrack_size -= (max_backtrack_size % NCA_PATCH_BLOCK_SIZE);
    while (matched_size < max_backtrack_size)
    {
        uint64_t read_size = max_backtrack_size - matched_size;
        if (read_size > sizeof(base_buffer))
        {
            read_size = sizeof(base_buffer);
        }
        read_size -= (read_size % NCA_PATCH_BLOCK_SIZE);

        if (!nca_cached_reader_try_read(base_reader, base_offset - matched_size - read_size, base_buffer, (size_t)read_size) ||
            !nca_cached_reader_try_read(current_reader, current_offset - matched_size - read_size, current_buffer, (size_t)read_size))
        {
            return matched_size;
        }

        if (memcmp(base_buffer, current_buffer, (size_t)read_size) == 0)
        {
            matched_size += read_size;
            continue;
        }

        for (uint64_t i = read_size; i > 0; i -= NCA_PATCH_BLOCK_SIZE)
        {
            if (memcmp(base_buffer + i - NCA_PATCH_BLOCK_SIZE, current_buffer + i - NCA_PATCH_BLOCK_SIZE, NCA_PATCH_BLOCK_SIZE) != 0)
            {
                return matched_size + (read_size - i);
            }
        }

        matched_size += read_size;
    }

    return matched_size;
}

static uint64_t nca_find_base_match(const nca_base_block_index_t *index, const nca_patch_hint_t *hints, uint32_t hint_count, nca_cached_reader_t *base_reader, uint64_t base_size, nca_cached_reader_t *current_reader, uint64_t current_size, uint64_t current_offset, const unsigned char *current_block, uint64_t current_block_fingerprint, uint64_t *out_base_offset)
{
    unsigned char base_block[NCA_PATCH_BLOCK_SIZE];
    uint64_t best_offset = 0;
    uint64_t best_size = 0;
    uint64_t indexed_match_size = 0;

    if (current_offset + NCA_PATCH_BLOCK_SIZE > current_size)
    {
        return 0;
    }

    {
        const nca_patch_hint_t *hint = nca_find_patch_hint(hints, hint_count, current_offset);
        if (hint != NULL)
        {
            uint64_t candidate_offset = hint->base_offset + (current_offset - hint->current_offset);
            uint64_t candidate_size = nca_measure_base_match(base_reader, base_size, candidate_offset, current_reader, current_size, current_offset);
            uint64_t hinted_remaining_size = hint->size - (current_offset - hint->current_offset);

            if (candidate_size > hinted_remaining_size)
            {
                candidate_size = hinted_remaining_size;
            }
            if (candidate_size >= NCA_PATCH_SAME_OFFSET_REUSE_MIN_SIZE)
            {
                best_offset = candidate_offset;
                best_size = candidate_size;
                if (best_size >= NCA_PATCH_GOOD_MATCH_SIZE)
                {
                    *out_base_offset = best_offset;
                    return best_size;
                }
            }
        }
    }

    if (current_offset + NCA_PATCH_BLOCK_SIZE <= base_size)
    {
        if (!nca_cached_reader_try_read(base_reader, current_offset, base_block, sizeof(base_block)))
        {
            FATAL_ERROR("Failed to read base RomFS section");
        }
        if (memcmp(base_block, current_block, NCA_PATCH_BLOCK_SIZE) == 0)
        {
            best_offset = current_offset;
            best_size = nca_measure_base_match(base_reader, base_size, current_offset, current_reader, current_size, current_offset);
            if (best_size >= NCA_PATCH_GOOD_MATCH_SIZE)
            {
                *out_base_offset = best_offset;
                return best_size;
            }
        }
    }

    for (uint64_t delta = NCA_PATCH_BLOCK_SIZE; delta <= NCA_PATCH_LOCAL_SEARCH_WINDOW; delta += NCA_PATCH_BLOCK_SIZE)
    {
        uint64_t candidate_offsets[2];
        uint32_t candidate_count = 0;

        if (current_offset >= delta)
        {
            candidate_offsets[candidate_count++] = current_offset - delta;
        }
        if (current_offset + delta + NCA_PATCH_BLOCK_SIZE <= base_size)
        {
            candidate_offsets[candidate_count++] = current_offset + delta;
        }

        for (uint32_t i = 0; i < candidate_count; i++)
        {
            uint64_t candidate_offset = candidate_offsets[i];
            uint64_t candidate_size;

            if (!nca_cached_reader_try_read(base_reader, candidate_offset, base_block, sizeof(base_block)))
            {
                continue;
            }
            if (memcmp(base_block, current_block, NCA_PATCH_BLOCK_SIZE) != 0)
            {
                continue;
            }

            candidate_size = nca_measure_base_match(base_reader, base_size, candidate_offset, current_reader, current_size, current_offset);
            if (candidate_size >= NCA_PATCH_RELOCATED_REUSE_MIN_SIZE && candidate_size > best_size)
            {
                best_offset = candidate_offset;
                best_size = candidate_size;
            }
        }

        if (best_size >= NCA_PATCH_GOOD_MATCH_SIZE)
        {
            break;
        }
    }

    {
        uint64_t indexed_match_offset = 0;
        indexed_match_size = nca_find_indexed_base_match(index, base_reader, base_size, current_block_fingerprint, current_reader, current_size, current_offset, &indexed_match_offset);
        if (indexed_match_size >= NCA_PATCH_GOOD_MATCH_SIZE && indexed_match_size > best_size)
        {
            best_offset = indexed_match_offset;
            best_size = indexed_match_size;
        }
    }

    if (best_size >= NCA_PATCH_SAME_OFFSET_REUSE_MIN_SIZE)
    {
        *out_base_offset = best_offset;
        return best_size;
    }

    return 0;
}

static void nca_extend_base_match_backwards(const nca_base_match_t *input_match, nca_cached_reader_t *base_reader, nca_cached_reader_t *current_reader, uint64_t pending_patch_offset, nca_base_match_t *out_match)
{
    uint64_t backtrack_size = 0;

    *out_match = *input_match;
    if (pending_patch_offset >= input_match->virtual_offset)
    {
        return;
    }

    backtrack_size = nca_measure_base_match_backwards(
        base_reader,
        input_match->base_offset,
        current_reader,
        input_match->virtual_offset,
        input_match->virtual_offset - pending_patch_offset);

    out_match->virtual_offset -= backtrack_size;
    out_match->base_offset -= backtrack_size;
    out_match->size += backtrack_size;
}

static void nca_build_patch_layout(FILE *base_file, uint64_t base_size, FILE *current_file, uint64_t current_size, const nca_patch_hint_t *hints, uint32_t hint_count, nca_patch_layout_t *layout)
{
    nca_base_block_index_t base_index;
    nca_cached_reader_t base_reader;
    nca_cached_reader_t current_reader;
    nca_current_block_cache_t current_block_cache;
    uint32_t capacity = 0;
    uint64_t pending_patch_offset = UINT64_MAX;
    static const uint64_t merge_thresholds[] = {0x20, 0x40, 0x80, 0x100, 0x200, 0x400};

    free(layout->segments);
    memset(layout, 0, sizeof(*layout));
    nca_base_block_index_init(&base_index);
    nca_cached_reader_init(&base_reader, base_file, base_size, NCA_PATCH_INDEX_READ_CHUNK);
    nca_cached_reader_init(&current_reader, current_file, current_size, NCA_PATCH_INDEX_READ_CHUNK);
    nca_current_block_cache_init(&current_block_cache, current_file, current_size, NCA_PATCH_INDEX_READ_CHUNK);

    if (base_file == NULL || base_size == 0)
    {
        nca_build_full_patch_layout(layout, current_size);
        nca_current_block_cache_free(&current_block_cache);
        nca_cached_reader_free(&current_reader);
        nca_cached_reader_free(&base_reader);
        return;
    }

    nca_build_base_block_index(base_file, base_size, &base_index);

    uint64_t offset = 0;
    while (offset < current_size)
    {
        nca_base_match_t base_match;
        uint64_t base_match_size;
        const unsigned char *current_block;
        uint64_t current_block_fingerprint = 0;

        memset(&base_match, 0, sizeof(base_match));
        base_match.virtual_offset = offset;
        base_match.size = 0;
        current_block = nca_current_block_cache_get_block(&current_block_cache, offset, &current_block_fingerprint);
        if (current_block == NULL)
        {
            FATAL_ERROR("Failed to read current RomFS block cache");
        }
        base_match_size = nca_find_base_match(&base_index, hints, hint_count, &base_reader, base_size, &current_reader, current_size, offset, current_block, current_block_fingerprint, &base_match.base_offset);
        base_match.size = base_match_size;

        if (base_match.size > 0)
        {
            if (pending_patch_offset != UINT64_MAX)
            {
                nca_extend_base_match_backwards(&base_match, &base_reader, &current_reader, pending_patch_offset, &base_match);
            }

            if (pending_patch_offset != UINT64_MAX)
            {
                nca_append_patch_data_segment(layout, &capacity, pending_patch_offset, base_match.virtual_offset - pending_patch_offset);
                pending_patch_offset = UINT64_MAX;
            }

            nca_append_base_segment(layout, &capacity, base_match.virtual_offset, base_match.size, base_match.base_offset);
            offset = base_match.virtual_offset + base_match.size;
        }
        else
        {
            uint64_t advance = NCA_PATCH_BLOCK_SIZE;

            if (pending_patch_offset == UINT64_MAX)
            {
                pending_patch_offset = offset;
            }

            advance = nca_choose_patch_probe_step((offset - pending_patch_offset) + NCA_PATCH_BLOCK_SIZE);
            if (offset + advance > current_size)
            {
                advance = current_size - offset;
                advance -= (advance % NCA_PATCH_BLOCK_SIZE);
                if (advance == 0)
                {
                    advance = NCA_PATCH_BLOCK_SIZE;
                }
            }

            offset += advance;
        }
    }

    if (pending_patch_offset != UINT64_MAX)
    {
        nca_append_patch_data_segment(layout, &capacity, pending_patch_offset, current_size - pending_patch_offset);
    }

    nca_finalize_patch_layout(layout);

    for (size_t i = 0; i < (sizeof(merge_thresholds) / sizeof(merge_thresholds[0])); i++)
    {
        if (layout->segment_count <= NCA_PATCH_SOFT_SEGMENT_LIMIT)
        {
            break;
        }
        nca_absorb_small_base_segments(layout, merge_thresholds[i]);
    }

    if (layout->segment_count == 0 || layout->segment_count > BKTR_MAX_RELOCATION_ENTRY_COUNT)
    {
        printf("BKTR diff still too fragmented, falling back to full replacement patch data\n");
        nca_build_full_patch_layout(layout, current_size);
    }

    nca_base_block_index_free(&base_index);
    nca_current_block_cache_free(&current_block_cache);
    nca_cached_reader_free(&current_reader);
    nca_cached_reader_free(&base_reader);
}

static nca_patch_hint_t *nca_build_patch_hints(const romfs_file_layout_entry_t *base_files, uint32_t base_file_count, uint64_t base_section_offset, const romfs_file_layout_entry_t *current_files, uint32_t current_file_count, uint64_t current_section_offset, uint32_t *out_hint_count)
{
    nca_patch_hint_t *hints = NULL;
    uint32_t hint_count = 0;
    bool *base_matched = NULL;
    bool *current_matched = NULL;
    uint64_t *base_signatures = NULL;
    uint64_t *current_signatures = NULL;
    nca_path_hash_table_t base_path_table;
    nca_signature_hash_table_t base_signature_table;
    nca_signature_hash_table_t current_signature_table;
    uint32_t unmatched_base_count = 0;
    uint32_t unmatched_current_count = 0;

    *out_hint_count = 0;
    if (base_files == NULL || current_files == NULL || base_file_count == 0 || current_file_count == 0)
    {
        return NULL;
    }

    hints = calloc((size_t)((base_file_count < current_file_count) ? base_file_count : current_file_count), sizeof(*hints));
    if (hints == NULL)
    {
        FATAL_ERROR("Failed to allocate RomFS patch hints");
    }

    base_matched = calloc(base_file_count, sizeof(*base_matched));
    current_matched = calloc(current_file_count, sizeof(*current_matched));
    base_signatures = calloc(base_file_count, sizeof(*base_signatures));
    current_signatures = calloc(current_file_count, sizeof(*current_signatures));
    if (base_matched == NULL || current_matched == NULL ||
        base_signatures == NULL || current_signatures == NULL)
    {
        free(hints);
        free(base_matched);
        free(current_matched);
        free(base_signatures);
        free(current_signatures);
        FATAL_ERROR("Failed to allocate RomFS patch hint metadata");
    }

    memset(&base_path_table, 0, sizeof(base_path_table));
    memset(&base_signature_table, 0, sizeof(base_signature_table));
    memset(&current_signature_table, 0, sizeof(current_signature_table));
    nca_path_hash_table_init(&base_path_table, base_file_count);
    for (uint32_t i = 0; i < base_file_count; i++)
    {
        nca_path_hash_table_insert(&base_path_table, base_files[i].path, i);
    }

    for (uint32_t current_file_index = 0; current_file_index < current_file_count; current_file_index++)
    {
        uint32_t matched_base_index = UINT32_MAX;
        if (nca_path_hash_table_find(&base_path_table, current_files[current_file_index].path, &matched_base_index))
        {
            uint64_t shared_size = base_files[matched_base_index].size;
            if (current_files[current_file_index].size < shared_size)
            {
                shared_size = current_files[current_file_index].size;
            }
            shared_size -= (shared_size % NCA_PATCH_BLOCK_SIZE);

            if (shared_size >= NCA_PATCH_SAME_OFFSET_REUSE_MIN_SIZE)
            {
                hints[hint_count].base_offset = base_section_offset + base_files[matched_base_index].offset;
                hints[hint_count].current_offset = current_section_offset + current_files[current_file_index].offset;
                hints[hint_count].size = shared_size;
                hint_count++;
                base_matched[matched_base_index] = true;
                current_matched[current_file_index] = true;
            }
        }
    }

    for (uint32_t i = 0; i < base_file_count; i++)
    {
        if (!base_matched[i])
        {
            unmatched_base_count++;
        }
    }
    for (uint32_t current_file_index = 0; current_file_index < current_file_count; current_file_index++)
    {
        if (current_matched[current_file_index])
        {
            continue;
        }
        unmatched_current_count++;
        current_signatures[current_file_index] = nca_compute_file_hint_signature(&current_files[current_file_index].source_path, current_files[current_file_index].size);
    }
    for (uint32_t base_file_index = 0; base_file_index < base_file_count; base_file_index++)
    {
        if (base_matched[base_file_index])
        {
            continue;
        }
        base_signatures[base_file_index] = nca_compute_file_hint_signature(&base_files[base_file_index].source_path, base_files[base_file_index].size);
    }

    nca_signature_hash_table_init(&current_signature_table, unmatched_current_count);
    nca_signature_hash_table_init(&base_signature_table, unmatched_base_count);
    for (uint32_t current_file_index = 0; current_file_index < current_file_count; current_file_index++)
    {
        if (!current_matched[current_file_index])
        {
            nca_signature_hash_table_insert(&current_signature_table, current_files[current_file_index].size, current_signatures[current_file_index], current_file_index);
        }
    }
    for (uint32_t base_file_index = 0; base_file_index < base_file_count; base_file_index++)
    {
        if (!base_matched[base_file_index])
        {
            nca_signature_hash_table_insert(&base_signature_table, base_files[base_file_index].size, base_signatures[base_file_index], base_file_index);
        }
    }

    for (uint32_t current_file_index = 0; current_file_index < current_file_count; current_file_index++)
    {
        const nca_signature_hash_entry_t *current_entry;
        const nca_signature_hash_entry_t *base_entry;

        if (current_matched[current_file_index])
        {
            continue;
        }
        current_entry = nca_signature_hash_table_find(&current_signature_table, current_files[current_file_index].size, current_signatures[current_file_index]);
        base_entry = nca_signature_hash_table_find(&base_signature_table, current_files[current_file_index].size, current_signatures[current_file_index]);
        if (current_entry == NULL || base_entry == NULL || current_entry->count != 1 || base_entry->count != 1 || base_matched[base_entry->index])
        {
            continue;
        }

        {
            uint64_t shared_size = current_files[current_file_index].size - (current_files[current_file_index].size % NCA_PATCH_BLOCK_SIZE);
            if (shared_size >= NCA_PATCH_SAME_OFFSET_REUSE_MIN_SIZE)
            {
                hints[hint_count].base_offset = base_section_offset + base_files[base_entry->index].offset;
                hints[hint_count].current_offset = current_section_offset + current_files[current_file_index].offset;
                hints[hint_count].size = shared_size;
                hint_count++;
                base_matched[base_entry->index] = true;
                current_matched[current_file_index] = true;
            }
        }
    }

    if (hint_count == 0)
    {
        free(hints);
        free(base_matched);
        free(current_matched);
        free(base_signatures);
        free(current_signatures);
        nca_path_hash_table_free(&base_path_table);
        nca_signature_hash_table_free(&base_signature_table);
        nca_signature_hash_table_free(&current_signature_table);
        return NULL;
    }

    qsort(hints, hint_count, sizeof(*hints), nca_compare_patch_hints);
    nca_merge_patch_hints(hints, &hint_count);
    free(base_matched);
    free(current_matched);
    free(base_signatures);
    free(current_signatures);
    nca_path_hash_table_free(&base_path_table);
    nca_signature_hash_table_free(&base_signature_table);
    nca_signature_hash_table_free(&current_signature_table);
    *out_hint_count = hint_count;
    return hints;
}

static void nca_copy_file_range(FILE *dst, uint64_t dst_offset, FILE *src, uint64_t src_offset, uint64_t size)
{
    uint64_t read_size = 0x400000;
    unsigned char *buffer = malloc(read_size);
    if (buffer == NULL)
    {
        FATAL_ERROR("Failed to allocate file copy buffer");
    }

    fseeko64(dst, dst_offset, SEEK_SET);
    fseeko64(src, src_offset, SEEK_SET);

    uint64_t copied = 0;
    while (copied < size)
    {
        if (copied + read_size > size)
        {
            read_size = size - copied;
        }

        if (fread(buffer, 1, read_size, src) != read_size)
        {
            free(buffer);
            FATAL_ERROR("Failed to read source range");
        }

        if (fwrite(buffer, 1, read_size, dst) != read_size)
        {
            free(buffer);
            FATAL_ERROR("Failed to write destination range");
        }

        copied += read_size;
    }

    free(buffer);
}

static uint64_t nca_build_romfs_section_data(hp_settings_t *settings, filepath_t *romfs_dir, const char *prefix, filepath_t *out_section_path, romfs_superblock_t *out_superblock, romfs_build_result_t *out_build_result)
{
    filepath_t ivfc_lvls_path[6];

    memset(out_superblock, 0, sizeof(*out_superblock));

    filepath_init(out_section_path);
    filepath_copy(out_section_path, &settings->temp_dir);
    filepath_append(out_section_path, "%s_section", prefix);

    for (int i = 0; i < 6; i++)
    {
        filepath_init(&ivfc_lvls_path[i]);
        filepath_copy(&ivfc_lvls_path[i], &settings->temp_dir);
        filepath_append(&ivfc_lvls_path[i], "%s_ivfc_lvl%i", prefix, i + 1);
    }

    printf("\n===> Building RomFS\n");
    if (out_build_result != NULL)
    {
        romfs_build_with_layout(romfs_dir, &ivfc_lvls_path[5], out_build_result);
        out_superblock->ivfc_header.level_headers[5].hash_data_size = out_build_result->image_size;
    }
    else
    {
        romfs_build(romfs_dir, &ivfc_lvls_path[5], &out_superblock->ivfc_header.level_headers[5].hash_data_size);
    }
    out_superblock->ivfc_header.level_headers[5].block_size = 0x0E;

    printf("\n===> Creating IVFC levels\n");
    for (int i = 4; i >= 0; i--)
    {
        printf("Writing %s\n", ivfc_lvls_path[i].char_path);
        ivfc_create_level(&ivfc_lvls_path[i], &ivfc_lvls_path[i + 1], &out_superblock->ivfc_header.level_headers[i].hash_data_size);
        out_superblock->ivfc_header.level_headers[i].block_size = 0x0E;
    }

    out_superblock->ivfc_header.level_headers[0].logical_offset = 0;
    for (int i = 1; i <= 5; i++)
    {
        out_superblock->ivfc_header.level_headers[i].logical_offset =
            out_superblock->ivfc_header.level_headers[i - 1].logical_offset +
            out_superblock->ivfc_header.level_headers[i - 1].hash_data_size;
    }

    out_superblock->ivfc_header.magic = MAGIC_IVFC;
    out_superblock->ivfc_header.id = 0x20000;
    out_superblock->ivfc_header.master_hash_size = 0x20;
    out_superblock->ivfc_header.num_levels = 0x7;

    printf("\n===> Calculating Hashes:\n");
    printf("Calculating Master hash\n");
    ivfc_calculate_master_hash(&ivfc_lvls_path[0], out_superblock->ivfc_header.master_hash);

    FILE *section_file = os_fopen(out_section_path->os_path, OS_MODE_WRITE_EDIT);
    if (section_file == NULL)
    {
        fprintf(stderr, "Failed to create %s!\n", out_section_path->char_path);
        exit(EXIT_FAILURE);
    }

    printf("\n===> Writing IVFC levels\n");
    for (int i = 0; i < 6; i++)
    {
        printf("Writing %s to %s\n", ivfc_lvls_path[i].char_path, out_section_path->char_path);
        nca_write_file(section_file, &ivfc_lvls_path[i]);
    }

    nca_write_padding(section_file);

    uint64_t section_size = (uint64_t)ftello64(section_file);
    fclose(section_file);

    return section_size;
}

static void nca_prepare_romfs_fs_header(nca_fs_header_t *fs_header, uint8_t crypt_type)
{
    fs_header->fs_type = FS_TYPE_ROMFS;
    fs_header->hash_type = HASH_TYPE_ROMFS;
    fs_header->version = 0x2;
    fs_header->crypt_type = crypt_type;
    fs_header->romfs_superblock.ivfc_header.magic = MAGIC_IVFC;
    fs_header->romfs_superblock.ivfc_header.id = 0x20000;
    fs_header->romfs_superblock.ivfc_header.master_hash_size = 0x20;
    fs_header->romfs_superblock.ivfc_header.num_levels = 0x7;
}

static uint64_t nca_build_patch_romfs_section(filepath_t *base_section_path, filepath_t *current_section_path, filepath_t *out_section_path, nca_fs_header_t *fs_header, const nca_patch_hint_t *hints, uint32_t hint_count)
{
    FILE *current_section = os_fopen(current_section_path->os_path, OS_MODE_READ);
    if (current_section == NULL)
    {
        fprintf(stderr, "Failed to open %s!\n", current_section_path->char_path);
        exit(EXIT_FAILURE);
    }

    FILE *base_section = NULL;
    if (base_section_path != NULL)
    {
        base_section = os_fopen(base_section_path->os_path, OS_MODE_READ);
        if (base_section == NULL)
        {
            fprintf(stderr, "Failed to open %s!\n", base_section_path->char_path);
            exit(EXIT_FAILURE);
        }
    }

    const uint64_t current_size = nca_get_file_size(current_section);
    const uint64_t base_size = (base_section != NULL) ? nca_get_file_size(base_section) : 0;

    nca_patch_layout_t layout;
    memset(&layout, 0, sizeof(layout));
    nca_build_patch_layout(base_section, base_size, current_section, current_size, hints, hint_count, &layout);

    FILE *patch_section = os_fopen(out_section_path->os_path, OS_MODE_WRITE_EDIT);
    if (patch_section == NULL)
    {
        fprintf(stderr, "Failed to create %s!\n", out_section_path->char_path);
        exit(EXIT_FAILURE);
    }

    printf("\n===> Writing BKTR patch data\n");
    for (uint32_t i = 0; i < layout.segment_count; i++)
    {
        if (layout.segments[i].is_patch == 0)
        {
            continue;
        }

        printf("Writing patch range 0x%012" PRIx64 " size 0x%012" PRIx64 "\n",
               layout.segments[i].virtual_offset,
               layout.segments[i].size);
        nca_copy_file_range(
            patch_section,
            layout.segments[i].physical_offset,
            current_section,
            layout.segments[i].virtual_offset,
            layout.segments[i].size);
    }

    nca_write_padding(patch_section);

    // Set section_ctr generation=1 (big-endian bytes [4..7]) for first-generation patch
    fs_header->section_ctr[4] = 0;
    fs_header->section_ctr[5] = 0;
    fs_header->section_ctr[6] = 0;
    fs_header->section_ctr[7] = 1;

    const uint64_t relocation_offset = (uint64_t)ftello64(patch_section);
    const uint32_t relocation_entry_count = layout.segment_count;
    const uint64_t relocation_table_size = bktr_get_relocation_table_size(relocation_entry_count);
    unsigned char *relocation_table = calloc(1, (size_t)relocation_table_size);
    bktr_subsection_entry_t subsection_entries[2];
    subsection_entries[0].offset = 0;
    subsection_entries[0].reserved = 0;
    subsection_entries[0].ctr_val = nca_get_section_generation(fs_header);
    subsection_entries[1].offset = relocation_offset;
    subsection_entries[1].reserved = 0;
    subsection_entries[1].ctr_val = 0;  // BKTR tables region uses generation=0
    const uint32_t subsection_entry_count = 2;
    const uint64_t subsection_table_size = bktr_get_subsection_table_size(subsection_entry_count);
    unsigned char *subsection_table = calloc(1, (size_t)subsection_table_size);
    if (relocation_table == NULL || subsection_table == NULL)
    {
        free(relocation_table);
        free(subsection_table);
        FATAL_ERROR("Failed to allocate BKTR tables");
    }

    bktr_build_relocation_table(relocation_table, relocation_table_size, current_size, layout.segments, relocation_entry_count);
    if (fwrite(relocation_table, 1, (size_t)relocation_table_size, patch_section) != relocation_table_size)
    {
        free(relocation_table);
        free(subsection_table);
        FATAL_ERROR("Failed to write BKTR relocation table");
    }

    const uint64_t subsection_offset = (uint64_t)ftello64(patch_section);
    const uint64_t section_size_predicted = subsection_offset + subsection_table_size;
    bktr_build_subsection_table(subsection_table, subsection_table_size, subsection_offset, section_size_predicted, subsection_entries, subsection_entry_count);
    if (fwrite(subsection_table, 1, (size_t)subsection_table_size, patch_section) != subsection_table_size)
    {
        free(relocation_table);
        free(subsection_table);
        FATAL_ERROR("Failed to write BKTR subsection table");
    }

    const uint64_t section_size = (uint64_t)ftello64(patch_section);

    free(relocation_table);
    free(subsection_table);
    free(layout.segments);

    fclose(patch_section);
    fclose(current_section);
    if (base_section != NULL)
    {
        fclose(base_section);
    }

    fs_header->crypt_type = CRYPT_BKTR;
    fs_header->bktr_superblock.relocation_header.offset = relocation_offset;
    fs_header->bktr_superblock.relocation_header.size = relocation_table_size;
    fs_header->bktr_superblock.relocation_header.magic = MAGIC_BKTR;
    fs_header->bktr_superblock.relocation_header.version = BKTR_VERSION;
    fs_header->bktr_superblock.relocation_header.num_entries = relocation_entry_count;
    fs_header->bktr_superblock.relocation_header.reserved = 0;
    fs_header->bktr_superblock.subsection_header.offset = subsection_offset;
    fs_header->bktr_superblock.subsection_header.size = subsection_table_size;
    fs_header->bktr_superblock.subsection_header.magic = MAGIC_BKTR;
    fs_header->bktr_superblock.subsection_header.version = BKTR_VERSION;
    fs_header->bktr_superblock.subsection_header.num_entries = subsection_entry_count;
    fs_header->bktr_superblock.subsection_header.reserved = 0;

    return section_size;
}

static uint64_t nca_prepare_romfs_section(hp_settings_t *settings, filepath_t *romfs_dir, filepath_t *base_romfs_dir, const char *prefix, filepath_t *out_section_path, nca_fs_header_t *fs_header)
{
    filepath_t current_section_path;
    filepath_t patch_section_path;
    filepath_t base_section_path;
    filepath_t *base_section_ptr = NULL;
    romfs_superblock_t base_superblock;
    romfs_build_result_t current_build;
    romfs_build_result_t base_build;
    nca_patch_hint_t *patch_hints = NULL;
    uint32_t patch_hint_count = 0;
    uint64_t profile_start = 0;

    memset(&current_build, 0, sizeof(current_build));
    memset(&base_build, 0, sizeof(base_build));

    if (settings->profile)
    {
        profile_start = nca_profile_now_ticks();
    }
    uint64_t current_size = nca_build_romfs_section_data(settings, romfs_dir, prefix, &current_section_path, &fs_header->romfs_superblock, settings->create_patch ? &current_build : NULL);
    if (settings->profile)
    {
        nca_profile_add(&settings->profile_romfs_current_ms, profile_start);
    }
    nca_prepare_romfs_fs_header(fs_header, settings->plaintext ? CRYPT_NONE : CRYPT_CTR);

    if (!settings->create_patch)
    {
        filepath_copy(out_section_path, &current_section_path);
        return current_size;
    }

    if (base_romfs_dir != NULL && base_romfs_dir->valid == VALIDITY_VALID)
    {
        char base_prefix[MAX_PATH];
        snprintf(base_prefix, sizeof(base_prefix), "%s_base", prefix);
        memset(&base_superblock, 0, sizeof(base_superblock));
        if (settings->profile)
        {
            profile_start = nca_profile_now_ticks();
        }
        nca_build_romfs_section_data(settings, base_romfs_dir, base_prefix, &base_section_path, &base_superblock, &base_build);
        if (settings->profile)
        {
            nca_profile_add(&settings->profile_romfs_base_ms, profile_start);
        }
        base_section_ptr = &base_section_path;

        if (settings->profile)
        {
            profile_start = nca_profile_now_ticks();
        }
        patch_hints = nca_build_patch_hints(
            base_build.layout.entries,
            base_build.layout.entry_count,
            base_superblock.ivfc_header.level_headers[5].logical_offset,
            current_build.layout.entries,
            current_build.layout.entry_count,
            fs_header->romfs_superblock.ivfc_header.level_headers[5].logical_offset,
            &patch_hint_count);
        if (settings->profile)
        {
            nca_profile_add(&settings->profile_patch_hints_ms, profile_start);
        }
    }

    filepath_init(&patch_section_path);
    filepath_copy(&patch_section_path, &settings->temp_dir);
    filepath_append(&patch_section_path, "%s_patch_section", prefix);

    filepath_copy(out_section_path, &patch_section_path);
    if (settings->profile)
    {
        profile_start = nca_profile_now_ticks();
    }
    uint64_t patch_size = nca_build_patch_romfs_section(base_section_ptr, &current_section_path, out_section_path, fs_header, patch_hints, patch_hint_count);
    if (settings->profile)
    {
        nca_profile_add(&settings->profile_patch_diff_ms, profile_start);
    }

    free(patch_hints);
    romfs_free_build_result(&current_build);
    romfs_free_build_result(&base_build);
    return patch_size;
}

void nca_create_romfs_type(hp_settings_t *settings, char *nca_type)
{
    printf("----> Creating %s NCA:\n", nca_type);
    printf("===> Creating NCA header\n");
    nca_header_t nca_header;
    memset(&nca_header, 0, sizeof(nca_header));

    filepath_t romfs_nca_path;
    filepath_init(&romfs_nca_path);
    filepath_copy(&romfs_nca_path, &settings->out_dir);
    filepath_append(&romfs_nca_path, "%s.nca", nca_type);

    FILE *romfs_nca_file;
    romfs_nca_file = os_fopen(romfs_nca_path.os_path, OS_MODE_WRITE_EDIT);

    // Write placeholder for NCA header
    printf("Writing NCA header placeholder to %s\n", romfs_nca_path.char_path);
    if (romfs_nca_file != NULL)
        fwrite(&nca_header, 1, sizeof(nca_header), romfs_nca_file);
    else
    {
        fprintf(stderr, "Failed to create %s!\n", romfs_nca_path.char_path);
        exit(EXIT_FAILURE);
    }

    printf("\n---> Creating Section 0:");

    filepath_t section0_path;
    filepath_init(&section0_path);
    nca_prepare_romfs_section(settings, &settings->romfs_dir, &settings->base_romfs_dir, nca_type, &section0_path, &nca_header.fs_headers[0]);

    nca_write_file(romfs_nca_file, &section0_path);
    nca_write_padding(romfs_nca_file);

    // Common values
    nca_header.magic = MAGIC_NCA3;
    nca_header.content_type = settings->nca_type;
    nca_header.sdk_version = settings->sdk_version;
    nca_header.title_id = settings->title_id;
    if (settings->nca_disttype == NCA_DISTRIBUTION_GAMECARD)
        nca_header.distribution = 1;
    nca_set_keygen(&nca_header, settings);

    nca_header.section_entries[0].media_start_offset = 0x6;                                        // 0xC00 / 0x200
    nca_header.section_entries[0].media_end_offset = (uint32_t)(ftello64(romfs_nca_file) / 0x200); // Section end offset / 200
    nca_header.section_entries[0]._0x8[0] = 0x1;                                                   // Always 1

    // Calculate section hash
    printf("\n===> Calculating Hashes:\n");
    printf("Calculating Section hash\n");
    nca_calculate_section_hash(&nca_header.fs_headers[0], nca_header.section_hashes[0]);

    printf("\n---> Finalizing:\n");

    if (settings->has_title_key == 0)
        // Set encrypted key area key 2
        memcpy(nca_header.encrypted_keys[2], settings->keyareakey, 0x10);
    else
    {
        // Calculate RightsID
        for (int ridc = 0; ridc < 8; ridc++)
        {
            nca_header.rights_id[7 - ridc] = (settings->title_id >> (8 * ridc) & 0xff);
        }
        nca_header.rights_id[15] = (uint8_t)settings->keygeneration;
    }

    printf("===> Encrypting NCA\n");
    if (settings->plaintext == 0)
    {
        // Encrypt section 0
        printf("Encrypting section 0\n");
        nca_encrypt_section(romfs_nca_file, &nca_header, 0, settings);
    }

    // Crypto type
    printf("Getting NCA file size\n");
    fseeko64(romfs_nca_file, 0, SEEK_END);
    nca_header.nca_size = (uint64_t)ftello64(romfs_nca_file);
    if (settings->has_title_key == 0)
    {
        printf("Encrypting key area\n");
        nca_encrypt_key_area(&nca_header, settings);
    }
    else
    {
        // Create cert and tik
        ticket_create_cert(settings);
        ticket_create_tik(settings);
    }

    // Fill NCA signature
    if (settings->nca_sig1_private_key.valid == VALIDITY_INVALID)
    {
        printf("Generating signature\n");
        nca_generate_sig(nca_header.fixed_key_sig, settings);
    }
    else
    {
        // Sign header with specified private key
        printf("Signing NCA header\n");
        rsa_sign_with_file(&nca_header.magic, 0x200, nca_header.fixed_key_sig, 0x100, settings->nca_sig1_private_key.char_path);
    }

    // Encrypt header
    printf("Encrypting header\n");
    nca_encrypt_header(&nca_header, settings);

    // Write NCA header
    printf("\n===> Writing NCA header\n");
    printf("Writing NCA header to %s\n", romfs_nca_path.char_path);
    fseeko64(romfs_nca_file, 0, SEEK_SET);
    fwrite(&nca_header, 1, sizeof(nca_header), romfs_nca_file);

    // Calculate hash and nca size
    printf("\n===> Post creation process\n");
    printf("Calculating NCA hash\n");
    unsigned char nca_hash[0x20];
    nca_calculate_hash(romfs_nca_file, nca_hash);

    fclose(romfs_nca_file);

    // Rename ncatype.nca to ncaid.nca
    filepath_t romfs_nca_final_path;
    filepath_init(&romfs_nca_final_path);
    filepath_copy(&romfs_nca_final_path, &settings->out_dir);
    char romfs_nca_name[37];
    hexBinaryString(nca_hash, 16, romfs_nca_name, 33);
    strcat(romfs_nca_name, ".nca");
    romfs_nca_name[36] = '\0';
    printf("Renaming %s.nca to %s\n", nca_type, romfs_nca_name);
    filepath_append(&romfs_nca_final_path, "%s", romfs_nca_name);
    os_rename(romfs_nca_path.os_path, romfs_nca_final_path.os_path);
    printf("\n----> Created %s NCA: %s\n", nca_type, romfs_nca_final_path.char_path);
}

void nca_create_program(hp_settings_t *settings)
{
    printf("----> Creating Program NCA:\n");
    printf("===> Creating NCA header\n");
    nca_header_t nca_header;
    memset(&nca_header, 0, sizeof(nca_header));

    filepath_t program_nca_path;
    filepath_init(&program_nca_path);
    filepath_copy(&program_nca_path, &settings->out_dir);
    filepath_append(&program_nca_path, "Program.nca");

    FILE *program_nca_file;
    program_nca_file = os_fopen(program_nca_path.os_path, OS_MODE_WRITE_EDIT);

    // Write placeholder for NCA header
    printf("Writing NCA header placeholder to %s\n", program_nca_path.char_path);
    if (program_nca_file != NULL)
        fwrite(&nca_header, 1, sizeof(nca_header), program_nca_file);
    else
    {
        fprintf(stderr, "Failed to create %s!\n", program_nca_path.char_path);
        exit(EXIT_FAILURE);
    }

    printf("\n---> Creating Section 0:");

    //Build ExeFS
    filepath_t program_exefs;
    filepath_init(&program_exefs);
    filepath_copy(&program_exefs, &settings->temp_dir);
    filepath_append(&program_exefs, "program_sec0_exefs");
    filepath_t program_exefs_hash_table;
    filepath_init(&program_exefs_hash_table);
    filepath_copy(&program_exefs_hash_table, &settings->temp_dir);
    filepath_append(&program_exefs_hash_table, "program_sec0_exefs_hashtable");
    uint32_t exefs_hash_block_size = PFS0_EXEFS_HASH_BLOCK_SIZE;
    printf("\n===> Building ExeFS\n");
    pfs0_build(&settings->exefs_dir, &program_exefs, &nca_header.fs_headers[0].pfs0_superblock.pfs0_size);
    printf("Calculating hash table\n");
    pfs0_create_hashtable(&program_exefs, &program_exefs_hash_table, exefs_hash_block_size, &nca_header.fs_headers[0].pfs0_superblock.hash_table_size, &nca_header.fs_headers[0].pfs0_superblock.pfs0_offset);

    // Write ExeFS
    printf("\n===> Writing ExeFS\n");
    printf("Writing PFS0 hash table\n");
    nca_write_file(program_nca_file, &program_exefs_hash_table);
    printf("Writing PFS0\n");
    nca_write_file(program_nca_file, &program_exefs);

    // Write Padding if required
    nca_write_padding(program_nca_file);

    // Common values
    nca_header.magic = MAGIC_NCA3;
    nca_header.content_type = 0x0; // Program
    nca_header.sdk_version = settings->sdk_version;
    nca_header.title_id = settings->title_id;
    if (settings->nca_disttype == NCA_DISTRIBUTION_GAMECARD)
        nca_header.distribution = 1;
    nca_set_keygen(&nca_header, settings);

    nca_header.section_entries[0].media_start_offset = 0x6;                                          // 0xC00 / 0x200
    nca_header.section_entries[0].media_end_offset = (uint32_t)(ftello64(program_nca_file) / 0x200); // Section end offset / 200
    nca_header.section_entries[0]._0x8[0] = 0x1;                                                     // Always 1

    nca_header.fs_headers[0].hash_type = HASH_TYPE_PFS0;
    nca_header.fs_headers[0].fs_type = FS_TYPE_PFS0;
    nca_header.fs_headers[0].version = 0x2; // Always 2
    nca_header.fs_headers[0].pfs0_superblock.always_2 = 0x2;
    nca_header.fs_headers[0].pfs0_superblock.block_size = exefs_hash_block_size;
    if (settings->plaintext == 0)
        nca_header.fs_headers[0].crypt_type = CRYPT_CTR;
    else
        nca_header.fs_headers[0].crypt_type = CRYPT_NONE;

    // Calculate master hash and section hash
    printf("\n===> Calculating Hashes:\n");
    printf("Calculating Master hash\n");
    pfs0_calculate_master_hash(&program_exefs_hash_table, nca_header.fs_headers[0].pfs0_superblock.hash_table_size, nca_header.fs_headers[0].pfs0_superblock.master_hash);
    printf("Calculating Section hash\n");
    nca_calculate_section_hash(&nca_header.fs_headers[0], nca_header.section_hashes[0]);

    if (settings->romfs_dir.valid == VALIDITY_VALID)
    {

        printf("\n---> Creating Section 1:");

        filepath_t section1_path;
        filepath_init(&section1_path);
        nca_prepare_romfs_section(settings, &settings->romfs_dir, &settings->base_romfs_dir, "program_sec1", &section1_path, &nca_header.fs_headers[1]);

        nca_write_file(program_nca_file, &section1_path);
        nca_write_padding(program_nca_file);

        // Set header values
        nca_header.section_entries[1].media_start_offset = nca_header.section_entries[0].media_end_offset;
        nca_header.section_entries[1].media_end_offset = (uint32_t)(ftello64(program_nca_file) / 0x200);
        nca_header.section_entries[1]._0x8[0] = 0x1; // Always 1

        // Calculate section hash
        printf("\n===> Calculating Hashes:\n");
        printf("Calculating Section hash\n");
        nca_calculate_section_hash(&nca_header.fs_headers[1], nca_header.section_hashes[1]);
    }

    if (settings->logo_dir.valid == VALIDITY_VALID)
    {
        printf("\n---> Creating Section 2:");

        //Build logo
        filepath_t program_logo;
        filepath_init(&program_logo);
        filepath_copy(&program_logo, &settings->temp_dir);
        filepath_append(&program_logo, "program_sec2_logo");
        filepath_t program_logo_hash_table;
        filepath_init(&program_logo_hash_table);
        filepath_copy(&program_logo_hash_table, &settings->temp_dir);
        filepath_append(&program_logo_hash_table, "program_sec2_logo_hashtable");
        uint32_t logo_hash_block_size = PFS0_LOGO_HASH_BLOCK_SIZE;
        printf("\n===> Building PFS0\n");
        pfs0_build(&settings->logo_dir, &program_logo, &nca_header.fs_headers[2].pfs0_superblock.pfs0_size);
        printf("Calculating hash table\n");
        pfs0_create_hashtable(&program_logo, &program_logo_hash_table, logo_hash_block_size, &nca_header.fs_headers[2].pfs0_superblock.hash_table_size, &nca_header.fs_headers[2].pfs0_superblock.pfs0_offset);

        // Write PFS0
        printf("\n===> Writing Logo\n");
        printf("Writing PFS0 hash table\n");
        nca_write_file(program_nca_file, &program_logo_hash_table);
        printf("Writing PFS0\n");
        nca_write_file(program_nca_file, &program_logo);

        // Write Padding if required
        nca_write_padding(program_nca_file);

        if (settings->romfs_dir.valid == VALIDITY_VALID)
            nca_header.section_entries[2].media_start_offset = nca_header.section_entries[1].media_end_offset;
        else
            nca_header.section_entries[2].media_start_offset = nca_header.section_entries[0].media_end_offset;

        nca_header.section_entries[2].media_end_offset = (uint32_t)(ftello64(program_nca_file) / 0x200); // Section end offset / 200
        nca_header.section_entries[2]._0x8[0] = 0x1;                                                     // Always 1

        nca_header.fs_headers[2].hash_type = HASH_TYPE_PFS0;
        nca_header.fs_headers[2].fs_type = FS_TYPE_PFS0;
        nca_header.fs_headers[2].version = 0x2;    // Always 2
        nca_header.fs_headers[2].crypt_type = 0x1; // Plain text
        nca_header.fs_headers[2].pfs0_superblock.always_2 = 0x2;
        nca_header.fs_headers[2].pfs0_superblock.block_size = logo_hash_block_size;

        // Calculate master hash and section hash
        printf("\n===> Calculating Hashes:\n");
        printf("Calculating Master hash\n");
        pfs0_calculate_master_hash(&program_logo_hash_table, nca_header.fs_headers[2].pfs0_superblock.hash_table_size, nca_header.fs_headers[2].pfs0_superblock.master_hash);
        printf("Calculating Section hash\n");
        nca_calculate_section_hash(&nca_header.fs_headers[2], nca_header.section_hashes[2]);
    }

    printf("\n---> Finalizing:\n");

    if (settings->has_title_key == 0)
        // Set encrypted key area key 2
        memcpy(nca_header.encrypted_keys[2], settings->keyareakey, 0x10);
    else
    {
        // Calculate RightsID
        for (int ridc = 0; ridc < 8; ridc++)
        {
            nca_header.rights_id[7 - ridc] = (settings->title_id >> (8 * ridc) & 0xff);
        }
        nca_header.rights_id[15] = (uint8_t)settings->keygeneration;
    }

    printf("===> Encrypting NCA\n");
    // Encrypt sections
    if (settings->plaintext == 0)
    {
        printf("Encrypting section 0\n");
        nca_encrypt_section(program_nca_file, &nca_header, 0, settings);
        if (settings->romfs_dir.valid == VALIDITY_VALID)
        {
            printf("Encrypting section 1\n");
            nca_encrypt_section(program_nca_file, &nca_header, 1, settings);
        }
    }

    // Crypto type
    printf("Getting NCA file size\n");
    fseeko64(program_nca_file, 0, SEEK_END);
    nca_header.nca_size = (uint64_t)ftello64(program_nca_file);
    if (settings->has_title_key == 0)
    {
        printf("Encrypting key area\n");
        nca_encrypt_key_area(&nca_header, settings);
    }
    else
    {
        // Create cert and tik
        ticket_create_cert(settings);
        ticket_create_tik(settings);
    }

    // Fill NCA signature
    if (settings->nca_sig1_private_key.valid == VALIDITY_INVALID)
    {
        printf("Generating signature\n");
        nca_generate_sig(nca_header.fixed_key_sig, settings);
    }
    else
    {
        // Sign header with specified private key
        printf("Signing NCA header\n");
        rsa_sign_with_file(&nca_header.magic, 0x200, nca_header.fixed_key_sig, 0x100, settings->nca_sig1_private_key.char_path);
    }

    // Sign header with acid public key (signature 2)
    if ((settings->noselfsignncasig2) == 0 || (settings->nca_sig2_private_key.valid == VALIDITY_VALID))
    {
        printf("Signing NCA header signature 2\n");
        if (settings->nca_sig2_private_key.valid == VALIDITY_VALID)
            rsa_sign_with_file(&nca_header.magic, 0x200, (unsigned char *)&nca_header.npdm_key_sig, 0x100, settings->nca_sig2_private_key.char_path);
        else
            rsa_sign(&nca_header.magic, 0x200, (unsigned char *)&nca_header.npdm_key_sig, 0x100, (char *)rsa_get_acid_private_key());
    }

    printf("Encrypting header\n");
    nca_encrypt_header(&nca_header, settings);

    // Write NCA header
    printf("\n===> Writing NCA header\n");
    printf("Writing NCA header to %s\n", program_nca_path.char_path);
    fseeko64(program_nca_file, 0, SEEK_SET);
    fwrite(&nca_header, 1, sizeof(nca_header), program_nca_file);

    // Calculate hash and nca size
    printf("\n===> Post creation process\n");
    printf("Calculating NCA hash\n");
    unsigned char nca_hash[0x20];
    nca_calculate_hash(program_nca_file, nca_hash);

    fclose(program_nca_file);

    // Rename Program.nca to ncaid.nca
    filepath_t program_nca_final_path;
    filepath_init(&program_nca_final_path);
    filepath_copy(&program_nca_final_path, &settings->out_dir);
    char program_nca_name[37];
    hexBinaryString(nca_hash, 16, program_nca_name, 33);
    strcat(program_nca_name, ".nca");
    program_nca_name[36] = '\0';
    printf("Renaming Program.nca to %s\n", program_nca_name);
    filepath_append(&program_nca_final_path, "%s", program_nca_name);
    os_rename(program_nca_path.os_path, program_nca_final_path.os_path);
    printf("\n----> Created Program NCA: %s\n", program_nca_final_path.char_path);
}

void nca_create_meta(hp_settings_t *settings)
{
    printf("----> Creating metadata NCA:\n");
    printf("===> Creating NCA header\n");
    nca_header_t nca_header;
    memset(&nca_header, 0, sizeof(nca_header));

    filepath_t meta_nca_path;
    filepath_init(&meta_nca_path);
    filepath_copy(&meta_nca_path, &settings->out_dir);
    filepath_append(&meta_nca_path, "Meta.nca");

    FILE *meta_nca_file;
    meta_nca_file = os_fopen(meta_nca_path.os_path, OS_MODE_WRITE_EDIT);

    // Write placeholder for NCA header
    printf("Writing NCA header placeholder to %s\n", meta_nca_path.char_path);
    if (meta_nca_file != NULL)
        fwrite(&nca_header, 1, sizeof(nca_header), meta_nca_file);
    else
    {
        fprintf(stderr, "Failed to create %s!\n", meta_nca_path.char_path);
        exit(EXIT_FAILURE);
    }

    filepath_t cnmt_path;
    filepath_init(&cnmt_path);
    filepath_copy(&cnmt_path, &settings->temp_dir);
    filepath_append(&cnmt_path, "cnmt");
    filepath_t cnmt_dir_path;
    filepath_init(&cnmt_dir_path);
    filepath_copy(&cnmt_dir_path, &cnmt_path);
    // Create cnmt directory if required
    os_makedir(cnmt_dir_path.os_path);
    // Cnmt filename = titletype_tid.cnmt
    printf("\n===> Creating Metadata file\n");
    if (settings->title_type == TITLE_TYPE_APPLICATION)
    {
        filepath_append(&cnmt_path, "Application_%016" PRIx64 ".cnmt", settings->title_id);
        if (settings->cnmt.valid == VALIDITY_VALID)
        {
            printf("Copying %s to %s\n", settings->cnmt.char_path, cnmt_path.char_path);
            filepath_copy_file(&settings->cnmt, &cnmt_path);
        }
        else
            cnmt_create_application(&cnmt_path, settings);
    }
    else if (settings->title_type == TITLE_TYPE_ADDON)
    {
        filepath_append(&cnmt_path, "AddOnContent_%016" PRIx64 ".cnmt", settings->title_id);
        if (settings->cnmt.valid == VALIDITY_VALID)
        {
            printf("Copying %s to %s\n", settings->cnmt.char_path, cnmt_path.char_path);
            filepath_copy_file(&settings->cnmt, &cnmt_path);
        }
        else
            cnmt_create_addon(&cnmt_path, settings);
    }
    else if (settings->title_type == TITLE_TYPE_SYSTEMPROGRAM)
    {
        filepath_append(&cnmt_path, "SystemProgram_%016" PRIx64 ".cnmt", settings->title_id);
        if (settings->cnmt.valid == VALIDITY_VALID)
        {
            printf("Copying %s to %s\n", settings->cnmt.char_path, cnmt_path.char_path);
            filepath_copy_file(&settings->cnmt, &cnmt_path);
        }
        else
            cnmt_create_systemprogram(&cnmt_path, settings);
    }
    else if (settings->title_type == TITLE_TYPE_SYSTEMDATA)
    {
        filepath_append(&cnmt_path, "SystemData_%016" PRIx64 ".cnmt", settings->title_id);
        if (settings->cnmt.valid == VALIDITY_VALID)
        {
            printf("Copying %s to %s\n", settings->cnmt.char_path, cnmt_path.char_path);
            filepath_copy_file(&settings->cnmt, &cnmt_path);
        }
        else
            cnmt_create_systemdata(&cnmt_path, settings);
    }
    else if (settings->title_type == TITLE_TYPE_PATCH)
    {
        filepath_append(&cnmt_path, "Patch_%016" PRIx64 ".cnmt", settings->title_id);
        if (settings->cnmt.valid == VALIDITY_VALID)
        {
            printf("Copying %s to %s\n", settings->cnmt.char_path, cnmt_path.char_path);
            filepath_copy_file(&settings->cnmt, &cnmt_path);
        }
        else
        {
            fprintf(stderr, "Creating Patch metadata without providing cnmt is not supported yet!\n");
            exit(EXIT_FAILURE);
        }
    }

    //Build PFS0
    filepath_t meta_pfs0;
    filepath_init(&meta_pfs0);
    filepath_copy(&meta_pfs0, &settings->temp_dir);
    filepath_append(&meta_pfs0, "meta_sec0_pfs0");
    filepath_t meta_pfs0_hash_table;
    filepath_init(&meta_pfs0_hash_table);
    filepath_copy(&meta_pfs0_hash_table, &settings->temp_dir);
    filepath_append(&meta_pfs0_hash_table, "meta_sec0_pfs0_hashtable");
    uint32_t meta_hash_block_size = PFS0_META_HASH_BLOCK_SIZE;
    printf("\n===> Building PFS0\n");
    pfs0_build(&cnmt_dir_path, &meta_pfs0, &nca_header.fs_headers[0].pfs0_superblock.pfs0_size);
    printf("Calculating hash table\n");
    pfs0_create_hashtable(&meta_pfs0, &meta_pfs0_hash_table, meta_hash_block_size, &nca_header.fs_headers[0].pfs0_superblock.hash_table_size, &nca_header.fs_headers[0].pfs0_superblock.pfs0_offset);

    // Write ExeFS
    printf("\n===> Writing PFS0 section\n");
    printf("Writing PFS0 hash table\n");
    nca_write_file(meta_nca_file, &meta_pfs0_hash_table);
    printf("Writing PFS0\n");
    nca_write_file(meta_nca_file, &meta_pfs0);

    // Write Padding if required
    nca_write_padding(meta_nca_file);

    // Common values
    nca_header.magic = MAGIC_NCA3;
    nca_header.content_type = 0x1; // Meta
    nca_header.sdk_version = settings->sdk_version;
    nca_header.title_id = settings->title_id;
    if (settings->nca_disttype == NCA_DISTRIBUTION_GAMECARD)
        nca_header.distribution = 1;
    nca_set_keygen(&nca_header, settings);

    nca_header.section_entries[0].media_start_offset = 0x6;                                       // 0xC00 / 0x200
    nca_header.section_entries[0].media_end_offset = (uint32_t)(ftello64(meta_nca_file) / 0x200); // Section end offset / 200
    nca_header.section_entries[0]._0x8[0] = 0x1;                                                  // Always 1

    nca_header.fs_headers[0].hash_type = HASH_TYPE_PFS0;
    nca_header.fs_headers[0].fs_type = FS_TYPE_PFS0;
    nca_header.fs_headers[0].version = 0x2; // Always 2
    nca_header.fs_headers[0].pfs0_superblock.always_2 = 0x2;
    nca_header.fs_headers[0].pfs0_superblock.block_size = meta_hash_block_size;
    if (settings->plaintext == 0)
        nca_header.fs_headers[0].crypt_type = CRYPT_CTR;
    else
        nca_header.fs_headers[0].crypt_type = CRYPT_NONE;

    // Calculate master hash and section hash
    printf("\n===> Calculating Hashes:\n");
    printf("Calculating Master hash\n");
    pfs0_calculate_master_hash(&meta_pfs0_hash_table, nca_header.fs_headers[0].pfs0_superblock.hash_table_size, nca_header.fs_headers[0].pfs0_superblock.master_hash);
    printf("Calculating Section hash\n");
    nca_calculate_section_hash(&nca_header.fs_headers[0], nca_header.section_hashes[0]);

    printf("\n---> Finalizing:\n");

    // Set encrypted key area key 2
    memcpy(nca_header.encrypted_keys[2], settings->keyareakey, 0x10);

    printf("===> Encrypting NCA\n");
    if (settings->plaintext == 0)
    {
        // Encrypt section 0
        printf("Encrypting section 0\n");
        nca_encrypt_section(meta_nca_file, &nca_header, 0, settings);
    }

    // Encrypt kek
    printf("Getting NCA file size\n");
    fseeko64(meta_nca_file, 0, SEEK_END);
    nca_header.nca_size = (uint64_t)ftello64(meta_nca_file);
    printf("Encrypting key area\n");
    nca_encrypt_key_area(&nca_header, settings);

    // Fill NCA signature
    if (settings->nca_sig1_private_key.valid == VALIDITY_INVALID)
    {
        printf("Generating signature\n");
        nca_generate_sig(nca_header.fixed_key_sig, settings);
    }
    else
    {
        // Sign header with specified private key
        printf("Signing NCA header\n");
        rsa_sign_with_file(&nca_header.magic, 0x200, nca_header.fixed_key_sig, 0x100, settings->nca_sig1_private_key.char_path);
    }

    // Encrypt header
    printf("Encrypting header\n");
    nca_encrypt_header(&nca_header, settings);

    // Write NCA header
    printf("\n===> Writing NCA header\n");
    printf("Writing NCA header to %s\n", meta_nca_path.char_path);
    fseeko64(meta_nca_file, 0, SEEK_SET);
    fwrite(&nca_header, 1, sizeof(nca_header), meta_nca_file);

    // Calculate hash and nca size
    printf("\n===> Post creation process\n");
    printf("Calculating NCA hash\n");
    unsigned char nca_hash[0x20];
    nca_calculate_hash(meta_nca_file, nca_hash);

    fclose(meta_nca_file);

    // Rename Meta.nca to ncaid.cnmt.nca
    filepath_t meta_nca_final_path;
    filepath_init(&meta_nca_final_path);
    filepath_copy(&meta_nca_final_path, &settings->out_dir);
    char meta_nca_name[42];
    hexBinaryString(nca_hash, 16, meta_nca_name, 33);
    strcat(meta_nca_name, ".cnmt.nca");
    meta_nca_name[41] = '\0';
    printf("Renaming Meta.nca to %s\n", meta_nca_name);
    filepath_append(&meta_nca_final_path, "%s", meta_nca_name);
    os_rename(meta_nca_path.os_path, meta_nca_final_path.os_path);
    printf("\n----> Created metadata NCA: %s\n", meta_nca_final_path.char_path);
}

void nca_write_file(FILE *nca_file, filepath_t *file_path)
{
    uint64_t file_size;
    FILE *fl;
    fl = os_fopen(file_path->os_path, OS_MODE_READ);

    if (fl == NULL)
    {
        fprintf(stderr, "Failed to open %s!\n", file_path->char_path);
        exit(EXIT_FAILURE);
    }

    // Get IVFC level file filesize
    fseeko64(fl, 0, SEEK_END);
    file_size = ftello64(fl);
    fseeko64(fl, 0, SEEK_SET);

    uint64_t read_size = 0x61A8000; // 100 MB buffer.
    unsigned char *buf = malloc(read_size);
    if (buf == NULL)
    {
        fprintf(stderr, "Failed to allocate file-read buffer!\n");
        exit(EXIT_FAILURE);
    }

    uint64_t ofs = 0;
    while (ofs < file_size)
    {
        if (ofs + read_size >= file_size)
            read_size = file_size - ofs;
        if (fread(buf, 1, read_size, fl) != read_size)
        {
            fprintf(stderr, "Failed to read file %s\n", file_path->char_path);
            exit(EXIT_FAILURE);
        }
        fwrite(buf, read_size, 1, nca_file);
        ofs += read_size;
    }

    free(buf);
    fclose(fl);
}

// Write padding for media_end_offset
void nca_write_padding(FILE *nca_file)
{
    unsigned char *buf = (unsigned char *)calloc(1, 0x200);
    uint64_t curr_offset = ftello64(nca_file);
    uint64_t block_size = 0x200;
    uint64_t padding_size = block_size - (curr_offset % block_size);
    if (curr_offset % block_size != 0)
        fwrite(buf, 1, padding_size, nca_file);
    free(buf);
}

void nca_calculate_section_hash(nca_fs_header_t *fs_header, uint8_t *out_section_hash)
{
    // Calculate hash
    sha_ctx_t *sha_ctx = new_sha_ctx(HASH_TYPE_SHA256, 0);
    sha_update(sha_ctx, fs_header, 0x200);
    sha_get_hash(sha_ctx, (unsigned char *)out_section_hash);
    free_sha_ctx(sha_ctx);
}

void nca_encrypt_key_area(nca_header_t *nca_header, hp_settings_t *settings)
{
    aes_ctx_t *aes_ctx = new_aes_ctx(settings->keyset.key_area_keys[settings->keygeneration - 1][0], 16, AES_MODE_ECB);
    aes_encrypt(aes_ctx, nca_header->encrypted_keys, nca_header->encrypted_keys, 0x40);
    free_aes_ctx(aes_ctx);
}

void nca_encrypt_header(nca_header_t *nca_header, hp_settings_t *settings)
{
    aes_ctx_t *hdr_aes_ctx = new_aes_ctx(settings->keyset.header_key, 32, AES_MODE_XTS);
    aes_xts_encrypt(hdr_aes_ctx, nca_header, nca_header, 0xC00, 0, 0x200);
    free_aes_ctx(hdr_aes_ctx);
}

/* Updates the CTR for a BKTR subsection: sets bytes [4..7] to ctr_val (big-endian)
   and bytes [8..15] to (ofs >> 4) (big-endian). Bytes [0..3] are left unchanged. */
static void nca_update_bktr_ctr(unsigned char *ctr, uint32_t ctr_val, uint64_t ofs)
{
    ofs >>= 4;
    for (unsigned int j = 0; j < 0x8; j++)
    {
        ctr[0x10 - j - 1] = (unsigned char)(ofs & 0xFF);
        ofs >>= 8;
    }
    for (unsigned int j = 0; j < 4; j++)
    {
        ctr[0x8 - j - 1] = (unsigned char)(ctr_val & 0xFF);
        ctr_val >>= 8;
    }
}

/* Encrypts a BKTR section region-by-region using the subsection table's ctr_val
   for each physical range, matching what hactool expects for decryption. */
static void nca_encrypt_bktr_section(FILE *nca_file, nca_header_t *nca_header, uint8_t section_index, hp_settings_t *settings)
{
    nca_fs_header_t *fs_header = &nca_header->fs_headers[section_index];
    uint64_t section_start = (uint64_t)nca_header->section_entries[section_index].media_start_offset * 0x200;
    uint64_t subsec_offset_in_file = section_start + fs_header->bktr_superblock.subsection_header.offset;
    uint64_t subsec_table_size = fs_header->bktr_superblock.subsection_header.size;

    void *subsec_table_buf = malloc((size_t)subsec_table_size);
    if (subsec_table_buf == NULL)
        FATAL_ERROR("Failed to allocate subsection table buffer for BKTR encryption");

    fseeko64(nca_file, subsec_offset_in_file, SEEK_SET);
    if (fread(subsec_table_buf, 1, (size_t)subsec_table_size, nca_file) != subsec_table_size)
    {
        free(subsec_table_buf);
        FATAL_ERROR("Failed to read subsection table for BKTR encryption");
    }

    bktr_subsection_block_t *subsec_block = (bktr_subsection_block_t *)subsec_table_buf;

    unsigned char enc_key[0x10];
    if (settings->has_title_key == 1)
        memcpy(enc_key, settings->title_key, 0x10);
    else
        memcpy(enc_key, nca_header->encrypted_keys[2], 0x10);
    aes_ctx_t *aes_ctx = new_aes_ctx(enc_key, 16, AES_MODE_CTR);

    /* Init CTR upper half from section_ctr (same layout as standard CTR sections) */
    unsigned char ctr[0x10] = {0};
    for (unsigned int j = 0; j < 0x8; j++)
        ctr[j] = fs_header->section_ctr[0x8 - j - 1];

    const uint64_t buf_size = 0x100000; /* 1 MB */
    unsigned char *buf = malloc((size_t)buf_size);
    if (buf == NULL)
    {
        free(subsec_table_buf);
        free_aes_ctx(aes_ctx);
        FATAL_ERROR("Failed to allocate encryption buffer for BKTR section");
    }

    /* Walk the subsection bucket tree; encrypt each physical region with its ctr_val */
    for (int32_t bi = 0; bi < subsec_block->num_buckets; bi++)
    {
        bktr_subsection_bucket_t *bucket = (bktr_subsection_bucket_t *)
            ((uint8_t *)subsec_table_buf + BKTR_NODE_SIZE + (uint64_t)bi * BKTR_NODE_SIZE);

        for (int32_t ei = 0; ei < bucket->num_entries; ei++)
        {
            uint64_t phys_start = bucket->entries[ei].offset;
            uint64_t phys_end;

            if (ei + 1 < bucket->num_entries)
            {
                phys_end = bucket->entries[ei + 1].offset;
            }
            else if (bi + 1 < subsec_block->num_buckets)
            {
                bktr_subsection_bucket_t *next_bucket = (bktr_subsection_bucket_t *)
                    ((uint8_t *)subsec_table_buf + BKTR_NODE_SIZE + (uint64_t)(bi + 1) * BKTR_NODE_SIZE);
                phys_end = next_bucket->entries[0].offset;
            }
            else
            {
                phys_end = (uint64_t)bucket->physical_offset_end;
            }

            uint32_t this_ctr_val = bucket->entries[ei].ctr_val;
            printf("  BKTR encrypt subsec[%d]: phys [0x%012" PRIx64 ", 0x%012" PRIx64 ") ctr_val=%u\n",
                   bi * (int32_t)BKTR_SUBSECTION_ENTRY_CAPACITY + ei, phys_start, phys_end, this_ctr_val);

            uint64_t ofs = phys_start;
            fseeko64(nca_file, section_start + phys_start, SEEK_SET);
            while (ofs < phys_end)
            {
                uint64_t to_read = phys_end - ofs;
                if (to_read > buf_size)
                    to_read = buf_size;
                if (fread(buf, 1, (size_t)to_read, nca_file) != to_read)
                {
                    free(buf);
                    free(subsec_table_buf);
                    free_aes_ctx(aes_ctx);
                    FATAL_ERROR("Read error during BKTR section encryption");
                }
                nca_update_bktr_ctr(ctr, this_ctr_val, section_start + ofs);
                aes_setiv(aes_ctx, ctr, 0x10);
                aes_encrypt(aes_ctx, buf, buf, (size_t)to_read);
                fseeko64(nca_file, section_start + ofs, SEEK_SET);
                if (fwrite(buf, 1, (size_t)to_read, nca_file) != to_read)
                {
                    free(buf);
                    free(subsec_table_buf);
                    free_aes_ctx(aes_ctx);
                    FATAL_ERROR("Write error during BKTR section encryption");
                }
                ofs += to_read;
            }
        }
    }

    free(buf);
    free(subsec_table_buf);
    free_aes_ctx(aes_ctx);
}

void nca_encrypt_section(FILE *nca_file, nca_header_t *nca_header, uint8_t section_index, hp_settings_t *settings)
{
    uint64_t profile_start = 0;
    if (settings->profile)
    {
        profile_start = nca_profile_now_ticks();
    }

    if (nca_header->fs_headers[section_index].crypt_type == CRYPT_BKTR)
    {
        nca_encrypt_bktr_section(nca_file, nca_header, section_index, settings);
    }
    else
    {
        uint64_t start_offset = nca_header->section_entries[section_index].media_start_offset;
        start_offset *= 0x200;
        uint64_t end_offset = nca_header->section_entries[section_index].media_end_offset;
        end_offset *= 0x200;
        uint64_t filesize = end_offset - start_offset;

        // Calculate counter for section encryption
        uint64_t ctr_ofs = start_offset >> 4;
        unsigned char ctr[0x10] = {0};
        for (unsigned int j = 0; j < 0x8; j++)
        {
            ctr[j] = nca_header->fs_headers[section_index].section_ctr[0x8 - j - 1];
            ctr[0x10 - j - 1] = (unsigned char)(ctr_ofs & 0xFF);
            ctr_ofs >>= 8;
        }

        uint64_t read_size = 0x6000000; //~100 MB buffer.
        unsigned char *buf = malloc(read_size);
        if (buf == NULL)
        {
            fprintf(stderr, "Failed to allocate file-read buffer!\n");
            exit(EXIT_FAILURE);
        }

        // Set Section encryption key
        unsigned char enc_key[0x10];
        if (settings->has_title_key == 1)
            memcpy(enc_key, settings->title_key, 0x10);
        else
            memcpy(enc_key, nca_header->encrypted_keys[2], 0x10);
        aes_ctx_t *aes_ctx = new_aes_ctx(enc_key, 16, AES_MODE_CTR);

        uint64_t ofs = 0;
        fseeko64(nca_file, start_offset, SEEK_SET);
        while (ofs < filesize)
        {
            if (ofs + read_size >= filesize)
                read_size = filesize - ofs;
            if (fread(buf, 1, read_size, nca_file) != read_size)
            {
                fprintf(stderr, "Failed to read file!\n");
                exit(EXIT_FAILURE);
            }
            fseeko64(nca_file, start_offset + ofs, SEEK_SET);
            aes_setiv(aes_ctx, ctr, 0x10);
            aes_encrypt(aes_ctx, buf, buf, read_size);
            fwrite(buf, 1, read_size, nca_file);
            ofs += read_size;
            nca_update_ctr(ctr, start_offset + ofs);
        }

        free(buf);
        free_aes_ctx(aes_ctx);
    }

    if (settings->profile)
    {
        nca_profile_add(&settings->profile_encrypt_ms, profile_start);
    }
}

/* Updates the CTR for an offset. */
void nca_update_ctr(unsigned char *ctr, uint64_t ofs)
{
    ofs >>= 4;
    for (unsigned int j = 0; j < 0x8; j++)
    {
        ctr[0x10 - j - 1] = (unsigned char)(ofs & 0xFF);
        ofs >>= 8;
    }
}

void nca_print_profile(const hp_settings_t *settings)
{
    if (!settings->profile)
    {
        return;
    }

    printf("\n----> Profile:\n");
    printf("romfs_current:  %.3f ms\n", settings->profile_romfs_current_ms);
    printf("romfs_base:     %.3f ms\n", settings->profile_romfs_base_ms);
    printf("layout_current: %.3f ms\n", settings->profile_layout_current_ms);
    printf("layout_base:    %.3f ms\n", settings->profile_layout_base_ms);
    printf("patch_hints:    %.3f ms\n", settings->profile_patch_hints_ms);
    printf("patch_diff:     %.3f ms\n", settings->profile_patch_diff_ms);
    printf("encrypt:        %.3f ms\n", settings->profile_encrypt_ms);
}

void nca_calculate_hash(FILE *nca_file, unsigned char *out_nca_hash)
{
    uint64_t file_size;
    // Get source file size
    fseeko64(nca_file, 0, SEEK_END);
    file_size = (uint64_t)ftello64(nca_file);

    sha_ctx_t *sha_ctx = new_sha_ctx(HASH_TYPE_SHA256, 0);
    uint64_t read_size = 0x61A8000; // 100 MB buffer.
    unsigned char *buf = malloc(read_size);
    fseeko64(nca_file, 0, SEEK_SET);

    if (buf == NULL)
    {
        fprintf(stderr, "Failed to allocate file-read buffer!\n");
        exit(EXIT_FAILURE);
    }

    uint64_t ofs = 0;
    while (ofs < file_size)
    {
        if (ofs + read_size >= file_size)
            read_size = file_size - ofs;
        if (fread(buf, 1, read_size, nca_file) != read_size)
        {
            fprintf(stderr, "Failed to read file!\n");
            exit(EXIT_FAILURE);
        }
        sha_update(sha_ctx, buf, read_size);
        ofs += read_size;
    }
    sha_get_hash(sha_ctx, out_nca_hash);

    free(buf);
    free_sha_ctx(sha_ctx);
}

void nca_set_keygen(nca_header_t *nca_header, hp_settings_t *settings)
{
    if (settings->keygeneration != 1)
    {
        if (settings->keygeneration == 2)
            nca_header->crypto_type = 0x2;
        else
        {
            nca_header->crypto_type = 0x2;
            nca_header->crypto_type2 = settings->keygeneration;
        }
    }
}

void nca_generate_sig(uint8_t *nca_sig, hp_settings_t *settings)
{
    switch (settings->nca_sig)
    {
    case NCA_SIG_TYPE_STATIC:
        memset(nca_sig, 4, 0x100);
        break;
    case NCA_SIG_TYPE_RANDOM:
        srand(time(NULL));
        for (long nsigc = 0; nsigc < 0x100; nsigc++)
            nca_sig[nsigc] = rand() % 0xff;
        break;
    case NCA_SIG_TYPE_ZERO:
        break;
    }
}

char *nca_romfs_get_type(uint8_t type)
{
    switch (type)
    {
    case NCA_TYPE_CONTROL:
        return "Control";
        break;
    case NCA_TYPE_DATA:
        return "Data";
        break;
    case NCA_TYPE_MANUAL:
        return "Manual";
        break;
    case NCA_TYPE_PUBLICDATA:
        return "PublicData";
        break;
    default:
        fprintf(stderr, "Unknown NCA type\n");
        exit(EXIT_FAILURE);
    }
}

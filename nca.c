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

typedef struct
{
    bktr_relocation_segment_t *segments;
    uint32_t segment_count;
    uint64_t patch_data_size;
} nca_patch_layout_t;

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

static void nca_read_file_exact(FILE *file, uint64_t offset, void *buffer, size_t size, const char *error_message);
static uint64_t nca_measure_base_match(FILE *base_file, uint64_t base_size, uint64_t base_offset, FILE *current_file, uint64_t current_size, uint64_t current_offset);
static int nca_try_read_file_exact(FILE *file, uint64_t offset, void *buffer, size_t size);

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
    uint32_t generation = 0;
    memcpy(&generation, fs_header->section_ctr, sizeof(generation));
    return generation;
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
    unsigned char block[NCA_PATCH_BLOCK_SIZE];
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

    while (base_offset + NCA_PATCH_BLOCK_SIZE <= base_size)
    {
        nca_read_file_exact(base_file, base_offset, block, sizeof(block), "Failed to read base RomFS section");
        nca_base_block_index_insert(index, nca_hash_block(block), base_offset);
        base_offset += NCA_PATCH_BLOCK_SIZE;
    }
}

static uint64_t nca_find_indexed_base_match(const nca_base_block_index_t *index, FILE *base_file, uint64_t base_size, const unsigned char *current_block, FILE *current_file, uint64_t current_size, uint64_t current_offset, uint64_t *out_base_offset)
{
    uint64_t fingerprint;
    uint32_t mask;
    uint32_t slot;
    uint64_t best_offset = 0;
    uint64_t best_size = 0;

    if (index->entries == NULL || index->slot_count == 0)
    {
        return 0;
    }

    fingerprint = nca_hash_block(current_block);
    mask = index->slot_count - 1;
    slot = (uint32_t)fingerprint & mask;

    for (uint32_t probe = 0; probe < NCA_PATCH_GLOBAL_INDEX_MAX_PROBES; probe++)
    {
        nca_base_block_index_entry_t *entry = &index->entries[(slot + probe) & mask];

        if (entry->fingerprint == 0)
        {
            break;
        }
        if (entry->fingerprint != fingerprint)
        {
            continue;
        }

        for (uint32_t candidate_index = 0; candidate_index < entry->candidate_count; candidate_index++)
        {
            uint64_t candidate_offset = entry->base_offsets[candidate_index];
            uint64_t candidate_size = nca_measure_base_match(base_file, base_size, candidate_offset, current_file, current_size, current_offset);

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

static void nca_read_file_exact(FILE *file, uint64_t offset, void *buffer, size_t size, const char *error_message)
{
    if (!nca_try_read_file_exact(file, offset, buffer, size))
    {
        FATAL_ERROR(error_message);
    }
}

static int nca_try_read_file_exact(FILE *file, uint64_t offset, void *buffer, size_t size)
{
    if (fseeko64(file, offset, SEEK_SET) != 0)
    {
        return 0;
    }

    return fread(buffer, 1, size, file) == size;
}

static uint64_t nca_measure_base_match(FILE *base_file, uint64_t base_size, uint64_t base_offset, FILE *current_file, uint64_t current_size, uint64_t current_offset)
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

        if (!nca_try_read_file_exact(base_file, base_offset + matched_size, base_buffer, (size_t)read_size) ||
            !nca_try_read_file_exact(current_file, current_offset + matched_size, current_buffer, (size_t)read_size))
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

static uint64_t nca_find_base_match(const nca_base_block_index_t *index, FILE *base_file, uint64_t base_size, FILE *current_file, uint64_t current_size, uint64_t current_offset, uint64_t *out_base_offset)
{
    unsigned char current_block[NCA_PATCH_BLOCK_SIZE];
    unsigned char base_block[NCA_PATCH_BLOCK_SIZE];
    uint64_t best_offset = 0;
    uint64_t best_size = 0;
    uint64_t indexed_match_size = 0;

    if (current_offset + NCA_PATCH_BLOCK_SIZE > current_size)
    {
        return 0;
    }

    nca_read_file_exact(current_file, current_offset, current_block, sizeof(current_block), "Failed to read current RomFS section");

    if (current_offset + NCA_PATCH_BLOCK_SIZE <= base_size)
    {
        nca_read_file_exact(base_file, current_offset, base_block, sizeof(base_block), "Failed to read base RomFS section");
        if (memcmp(base_block, current_block, sizeof(current_block)) == 0)
        {
            best_offset = current_offset;
            best_size = nca_measure_base_match(base_file, base_size, current_offset, current_file, current_size, current_offset);
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

            if (!nca_try_read_file_exact(base_file, candidate_offset, base_block, sizeof(base_block)))
            {
                continue;
            }
            if (memcmp(base_block, current_block, sizeof(current_block)) != 0)
            {
                continue;
            }

            candidate_size = nca_measure_base_match(base_file, base_size, candidate_offset, current_file, current_size, current_offset);
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
        indexed_match_size = nca_find_indexed_base_match(index, base_file, base_size, current_block, current_file, current_size, current_offset, &indexed_match_offset);
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

static void nca_build_patch_layout(FILE *base_file, uint64_t base_size, FILE *current_file, uint64_t current_size, nca_patch_layout_t *layout)
{
    nca_base_block_index_t base_index;
    uint32_t capacity = 0;
    uint64_t pending_patch_offset = UINT64_MAX;
    static const uint64_t merge_thresholds[] = {0x20, 0x40, 0x80, 0x100, 0x200, 0x400};

    free(layout->segments);
    memset(layout, 0, sizeof(*layout));
    nca_base_block_index_init(&base_index);

    if (base_file == NULL || base_size == 0)
    {
        nca_build_full_patch_layout(layout, current_size);
        return;
    }

    nca_build_base_block_index(base_file, base_size, &base_index);

    uint64_t offset = 0;
    while (offset < current_size)
    {
        uint64_t base_match_offset = 0;
        uint64_t base_match_size = nca_find_base_match(&base_index, base_file, base_size, current_file, current_size, offset, &base_match_offset);

        if (base_match_size > 0)
        {
            if (pending_patch_offset != UINT64_MAX)
            {
                nca_append_patch_data_segment(layout, &capacity, pending_patch_offset, offset - pending_patch_offset);
                pending_patch_offset = UINT64_MAX;
            }

            nca_append_base_segment(layout, &capacity, offset, base_match_size, base_match_offset);
            offset += base_match_size;
        }
        else
        {
            if (pending_patch_offset == UINT64_MAX)
            {
                pending_patch_offset = offset;
            }
            offset += NCA_PATCH_BLOCK_SIZE;
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

static uint64_t nca_build_romfs_section_data(hp_settings_t *settings, filepath_t *romfs_dir, const char *prefix, filepath_t *out_section_path, romfs_superblock_t *out_superblock)
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
    romfs_build(romfs_dir, &ivfc_lvls_path[5], &out_superblock->ivfc_header.level_headers[5].hash_data_size);
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

static uint64_t nca_build_patch_romfs_section(filepath_t *base_section_path, filepath_t *current_section_path, filepath_t *out_section_path, nca_fs_header_t *fs_header)
{
    bktr_subsection_entry_t subsection_entry;
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
    nca_build_patch_layout(base_section, base_size, current_section, current_size, &layout);

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

    const uint64_t relocation_offset = (uint64_t)ftello64(patch_section);
    const uint32_t relocation_entry_count = layout.segment_count;
    const uint64_t relocation_table_size = bktr_get_relocation_table_size(relocation_entry_count);
    unsigned char *relocation_table = calloc(1, (size_t)relocation_table_size);
    subsection_entry.offset = 0;
    subsection_entry.reserved = 0;
    subsection_entry.ctr_val = nca_get_section_generation(fs_header);
    const uint32_t subsection_entry_count = 1;
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
    bktr_build_subsection_table(subsection_table, subsection_table_size, subsection_offset, relocation_offset, &subsection_entry, subsection_entry_count);
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

    uint64_t current_size = nca_build_romfs_section_data(settings, romfs_dir, prefix, &current_section_path, &fs_header->romfs_superblock);
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
        nca_build_romfs_section_data(settings, base_romfs_dir, base_prefix, &base_section_path, &base_superblock);
        base_section_ptr = &base_section_path;
    }

    filepath_init(&patch_section_path);
    filepath_copy(&patch_section_path, &settings->temp_dir);
    filepath_append(&patch_section_path, "%s_patch_section", prefix);

    filepath_copy(out_section_path, &patch_section_path);
    return nca_build_patch_romfs_section(base_section_ptr, &current_section_path, out_section_path, fs_header);
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

void nca_encrypt_section(FILE *nca_file, nca_header_t *nca_header, uint8_t section_index, hp_settings_t *settings)
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

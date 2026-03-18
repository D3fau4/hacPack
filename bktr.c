#include <string.h>
#include "bktr.h"
#include "utils.h"

static void bktr_validate_relocation_segment_count(uint32_t segment_count)
{
    if (segment_count == 0 || segment_count > BKTR_RELOCATION_ENTRY_CAPACITY)
    {
        FATAL_ERROR("invalid BKTR relocation segment count");
    }
}

void bktr_build_relocation_table(void *buffer, uint64_t virtual_size, const bktr_relocation_segment_t *segments, uint32_t segment_count)
{
    bktr_validate_relocation_segment_count(segment_count);

    memset(buffer, 0, BKTR_RELOCATION_TABLE_SIZE);

    bktr_relocation_block_t *block = (bktr_relocation_block_t *)buffer;
    block->index = 0;
    block->num_buckets = 1;
    block->total_size = (int64_t)virtual_size;
    block->bucket_virtual_offsets[0] = (int64_t)segments[0].virtual_offset;

    bktr_relocation_bucket_t *bucket = block->buckets;
    bucket->index = 0;
    bucket->num_entries = (int32_t)segment_count;
    bucket->virtual_offset_end = (int64_t)virtual_size;

    for (uint32_t i = 0; i < segment_count; i++)
    {
        bucket->entries[i].virt_offset = segments[i].virtual_offset;
        bucket->entries[i].phys_offset = segments[i].physical_offset;
        bucket->entries[i].is_patch = segments[i].is_patch;
    }
}

void bktr_build_subsection_table(void *buffer, uint64_t total_size, uint64_t patch_data_size, uint32_t generation)
{
    memset(buffer, 0, BKTR_SUBSECTION_TABLE_SIZE);

    bktr_subsection_block_t *block = (bktr_subsection_block_t *)buffer;
    block->index = 0;
    block->num_buckets = 1;
    block->total_size = (int64_t)total_size;
    block->bucket_physical_offsets[0] = 0;

    bktr_subsection_bucket_t *bucket = block->buckets;
    bucket->index = 0;
    bucket->num_entries = 1;
    bucket->physical_offset_end = (int64_t)patch_data_size;

    bucket->entries[0].offset = 0;
    bucket->entries[0].reserved = 0;
    bucket->entries[0].ctr_val = generation;
}

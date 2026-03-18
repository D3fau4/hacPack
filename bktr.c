#include <stdlib.h>
#include <string.h>
#include "bktr.h"
#include "utils.h"

static uint32_t bktr_get_bucket_count(uint32_t entry_count, uint32_t bucket_capacity)
{
    if (entry_count == 0)
    {
        FATAL_ERROR("invalid BKTR entry count");
    }

    return (entry_count + bucket_capacity - 1) / bucket_capacity;
}

static void bktr_validate_bucket_count(uint32_t bucket_count)
{
    if (bucket_count == 0 || bucket_count > BKTR_MAX_BUCKET_COUNT)
    {
        FATAL_ERROR("invalid BKTR bucket count");
    }
}

uint64_t bktr_get_relocation_table_size(uint32_t segment_count)
{
    if (segment_count == 0 || segment_count > BKTR_MAX_RELOCATION_ENTRY_COUNT)
    {
        FATAL_ERROR("invalid BKTR relocation segment count");
    }

    return BKTR_NODE_SIZE + ((uint64_t)bktr_get_bucket_count(segment_count, BKTR_RELOCATION_ENTRY_CAPACITY) * BKTR_NODE_SIZE);
}

uint64_t bktr_get_subsection_table_size(uint32_t entry_count)
{
    if (entry_count == 0 || entry_count > BKTR_MAX_SUBSECTION_ENTRY_COUNT)
    {
        FATAL_ERROR("invalid BKTR subsection entry count");
    }

    return BKTR_NODE_SIZE + ((uint64_t)bktr_get_bucket_count(entry_count, BKTR_SUBSECTION_ENTRY_CAPACITY) * BKTR_NODE_SIZE);
}

void bktr_build_relocation_table(void *buffer, uint64_t buffer_size, uint64_t virtual_size, const bktr_relocation_segment_t *segments, uint32_t segment_count)
{
    uint64_t expected_size = bktr_get_relocation_table_size(segment_count);
    uint32_t bucket_count = bktr_get_bucket_count(segment_count, BKTR_RELOCATION_ENTRY_CAPACITY);
    bktr_validate_bucket_count(bucket_count);

    if (buffer_size != expected_size)
    {
        FATAL_ERROR("invalid BKTR relocation table size");
    }

    memset(buffer, 0, (size_t)buffer_size);

    bktr_relocation_block_t *block = (bktr_relocation_block_t *)buffer;
    block->index = 0;
    block->num_buckets = (int32_t)bucket_count;
    block->total_size = (int64_t)virtual_size;

    for (uint32_t bucket_index = 0; bucket_index < bucket_count; bucket_index++)
    {
        uint32_t first_entry_index = bucket_index * BKTR_RELOCATION_ENTRY_CAPACITY;
        uint32_t bucket_entry_count = segment_count - first_entry_index;
        if (bucket_entry_count > BKTR_RELOCATION_ENTRY_CAPACITY)
        {
            bucket_entry_count = BKTR_RELOCATION_ENTRY_CAPACITY;
        }

        block->bucket_virtual_offsets[bucket_index] = (int64_t)segments[first_entry_index].virtual_offset;

        bktr_relocation_bucket_t *bucket =
            (bktr_relocation_bucket_t *)((uint8_t *)buffer + BKTR_NODE_SIZE + ((uint64_t)bucket_index * BKTR_NODE_SIZE));
        bucket->index = (int32_t)bucket_index;
        bucket->num_entries = (int32_t)bucket_entry_count;
        if (bucket_index + 1 < bucket_count)
        {
            bucket->virtual_offset_end = (int64_t)segments[first_entry_index + bucket_entry_count].virtual_offset;
        }
        else
        {
            bucket->virtual_offset_end = (int64_t)virtual_size;
        }

        for (uint32_t i = 0; i < bucket_entry_count; i++)
        {
            bucket->entries[i].virt_offset = segments[first_entry_index + i].virtual_offset;
            bucket->entries[i].phys_offset = segments[first_entry_index + i].physical_offset;
            bucket->entries[i].is_patch = segments[first_entry_index + i].is_patch;
        }
    }
}

void bktr_build_subsection_table(void *buffer, uint64_t buffer_size, uint64_t total_size, uint64_t patch_data_size, const bktr_subsection_entry_t *entries, uint32_t entry_count)
{
    uint64_t expected_size = bktr_get_subsection_table_size(entry_count);
    uint32_t bucket_count = bktr_get_bucket_count(entry_count, BKTR_SUBSECTION_ENTRY_CAPACITY);
    bktr_validate_bucket_count(bucket_count);

    if (buffer_size != expected_size)
    {
        FATAL_ERROR("invalid BKTR subsection table size");
    }

    memset(buffer, 0, (size_t)buffer_size);

    bktr_subsection_block_t *block = (bktr_subsection_block_t *)buffer;
    block->index = 0;
    block->num_buckets = (int32_t)bucket_count;
    block->total_size = (int64_t)total_size;

    for (uint32_t bucket_index = 0; bucket_index < bucket_count; bucket_index++)
    {
        uint32_t first_entry_index = bucket_index * BKTR_SUBSECTION_ENTRY_CAPACITY;
        uint32_t bucket_entry_count = entry_count - first_entry_index;
        if (bucket_entry_count > BKTR_SUBSECTION_ENTRY_CAPACITY)
        {
            bucket_entry_count = BKTR_SUBSECTION_ENTRY_CAPACITY;
        }

        block->bucket_physical_offsets[bucket_index] = (int64_t)entries[first_entry_index].offset;

        bktr_subsection_bucket_t *bucket =
            (bktr_subsection_bucket_t *)((uint8_t *)buffer + BKTR_NODE_SIZE + ((uint64_t)bucket_index * BKTR_NODE_SIZE));
        bucket->index = (int32_t)bucket_index;
        bucket->num_entries = (int32_t)bucket_entry_count;
        if (bucket_index + 1 < bucket_count)
        {
            bucket->physical_offset_end = (int64_t)entries[first_entry_index + bucket_entry_count].offset;
        }
        else
        {
            bucket->physical_offset_end = (int64_t)patch_data_size;
        }

        for (uint32_t i = 0; i < bucket_entry_count; i++)
        {
            bucket->entries[i] = entries[first_entry_index + i];
        }
    }
}

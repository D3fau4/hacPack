#ifndef HACPACK_BKTR_H
#define HACPACK_BKTR_H

#include <stdint.h>

#define MAGIC_BKTR 0x52544B42
#define BKTR_VERSION 0x00000001
#define BKTR_NODE_SIZE 0x4000
#define BKTR_MAX_BUCKET_COUNT (0x3FF0 / sizeof(int64_t))
#define BKTR_RELOCATION_ENTRY_CAPACITY (0x3FF0 / sizeof(bktr_relocation_entry_t))
#define BKTR_SUBSECTION_ENTRY_CAPACITY 0x3FF
#define BKTR_MAX_RELOCATION_ENTRY_COUNT (BKTR_MAX_BUCKET_COUNT * BKTR_RELOCATION_ENTRY_CAPACITY)
#define BKTR_MAX_SUBSECTION_ENTRY_COUNT (BKTR_MAX_BUCKET_COUNT * BKTR_SUBSECTION_ENTRY_CAPACITY)

#pragma pack(push, 1)
typedef struct
{
    uint64_t offset;
    uint64_t size;
    uint32_t magic;
    uint32_t version;
    uint32_t num_entries;
    uint32_t reserved;
} bktr_header_t;
#pragma pack(pop)

#pragma pack(push, 1)
typedef struct
{
    uint64_t virt_offset;
    uint64_t phys_offset;
    uint32_t is_patch;
} bktr_relocation_entry_t;
#pragma pack(pop)

#pragma pack(push, 1)
typedef struct
{
    int32_t index;
    int32_t num_entries;
    int64_t virtual_offset_end;
    bktr_relocation_entry_t entries[BKTR_RELOCATION_ENTRY_CAPACITY];
    uint8_t padding[0x3FF0 % sizeof(bktr_relocation_entry_t)];
} bktr_relocation_bucket_t;
#pragma pack(pop)

#pragma pack(push, 1)
typedef struct
{
    int32_t index;
    int32_t num_buckets;
    int64_t total_size;
    int64_t bucket_virtual_offsets[0x3FF0 / sizeof(int64_t)];
    bktr_relocation_bucket_t buckets[];
} bktr_relocation_block_t;
#pragma pack(pop)

#pragma pack(push, 1)
typedef struct
{
    uint64_t offset;
    uint32_t reserved;
    uint32_t ctr_val;
} bktr_subsection_entry_t;
#pragma pack(pop)

#pragma pack(push, 1)
typedef struct
{
    int32_t index;
    int32_t num_entries;
    int64_t physical_offset_end;
    bktr_subsection_entry_t entries[BKTR_SUBSECTION_ENTRY_CAPACITY];
} bktr_subsection_bucket_t;
#pragma pack(pop)

#pragma pack(push, 1)
typedef struct
{
    int32_t index;
    int32_t num_buckets;
    int64_t total_size;
    int64_t bucket_physical_offsets[0x3FF0 / sizeof(int64_t)];
    bktr_subsection_bucket_t buckets[];
} bktr_subsection_block_t;
#pragma pack(pop)

typedef struct
{
    uint64_t virtual_offset;
    uint64_t size;
    uint64_t physical_offset;
    uint32_t is_patch;
} bktr_relocation_segment_t;

uint64_t bktr_get_relocation_table_size(uint32_t segment_count);
uint64_t bktr_get_subsection_table_size(uint32_t entry_count);
void bktr_build_relocation_table(void *buffer, uint64_t buffer_size, uint64_t virtual_size, const bktr_relocation_segment_t *segments, uint32_t segment_count);
void bktr_build_subsection_table(void *buffer, uint64_t buffer_size, uint64_t total_size, uint64_t patch_data_size, const bktr_subsection_entry_t *entries, uint32_t entry_count);

#endif

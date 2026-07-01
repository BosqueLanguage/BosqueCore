#pragma once

#include "./flagmgr.h"

/**
 * This file contains the flags that are used to enable and disable various features and diagnostics in the runtime. 
 * Also contains GC specific performance flags (nursery size etc.) are in the allocator/flags.h file. 
 **/

//Control for page sizes and access
#define GC_BITS_IN_ADDR_FOR_PAGE 12ul
#define GC_PAGE_SIZE (1ul << GC_BITS_IN_ADDR_FOR_PAGE)
#define GC_BLOCK_ALLOCATION_SIZE (1ul << GC_BITS_IN_ADDR_FOR_PAGE)
#define GC_PAGE_MASK ((1ul << GC_BITS_IN_ADDR_FOR_PAGE) - 1ul)
#define GC_PAGE_ADDR_MASK (~GC_PAGE_MASK)

namespace ᐸRuntimeᐳ
{
    //Bosque runtime debugging and diagnostic flags
    BSQ_REGISTER_FLAG(RB_INVARIANT_VALIDATE, "Enable red-black tree validation checks");

    //GC debugging and diagnostics flags
    GC_REGISTER_FLAG(GC_CLEAR_EAGER_FEATURE, "Process all pages immediately after collection");
    GC_REGISTER_FLAG(GC_MEMORY_CLEAR_FEATURE, "Zero out memory when processing pages and RC free");
    GC_REGISTER_FLAG(GC_ALLOW_NON_DETERMINISTIC_MMAP, "Allow non-deterministic mmap allocations for GC pages");

    //Feature flags for in progress work
    GC_REGISTER_FLAG(GC_UNIQUE_PARENT_FEATURE, "Enable unique parent tracking for RC objects");

    //Support for computing GC metrics
    GC_REGISTER_FLAG(GC_METRICS, "Enable basic GC metrics collection");

#if GC_NURSERY_BYTES_COLLECT_THRESHOLD
    GC_REGISTER_PARAMETER(int64_t, GC_NURSERY_BYTES_COLLECT_THRESHOLD, "The number of bytes allocated in the nursery before a collection is triggered");
#else
    GC_REGISTER_PARAMETER_DEFAULT(int64_t, GC_NURSERY_BYTES_COLLECT_THRESHOLD, 1ul << 20);
#endif

#if GC_DELETE_PENDING_PROCESS_BYTES_COLLECT
    GC_REGISTER_PARAMETER(int64_t, GC_DELETE_PENDING_PROCESS_BYTES_COLLECT, "The number of bytes to process from the pending delete list during a collection");
#else 
    GC_REGISTER_PARAMETER_DEFAULT(int64_t, GC_DELETE_PENDING_PROCESS_BYTES_COLLECT, (GC_GET_PARAMETER(GC_NURSERY_BYTES_COLLECT_THRESHOLD) / 2));
#endif

#if GC_DELETE_PENDING_PROCESS_BYTES_INCREMENTAL
    GC_REGISTER_PARAMETER(int64_t, GC_DELETE_PENDING_PROCESS_BYTES_INCREMENTAL, "The number of bytes to process from the pending delete list during a collection");
#else 
    GC_REGISTER_PARAMETER_DEFAULT(int64_t, GC_DELETE_PENDING_PROCESS_BYTES_INCREMENTAL, (GC_PAGE_SIZE / 2));
#endif

#if GC_NUM_PAGES_ON_REQ
    GC_REGISTER_PARAMETER(int64_t, GC_NUM_PAGES_ON_REQ, "The number of pages to allocate on a single request");
#else
    GC_REGISTER_PARAMETER_DEFAULT(int64_t, GC_NUM_PAGES_ON_REQ, 4);
#endif

#if GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC
    GC_REGISTER_PARAMETER(double, GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC, "The ratio of free slots in a page to consider it for allocation");
#else
    GC_REGISTER_PARAMETER_DEFAULT(double, GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC, 0.60);
#endif

#if GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC
    GC_REGISTER_PARAMETER(double, GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC, "The ratio of free slots in a page to consider it for evacuation");
#else
    GC_REGISTER_PARAMETER_DEFAULT(double, GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC, 0.30);
#endif

#if GC_PAGE_CHECK_NURSERY_LIMIT
    GC_REGISTER_PARAMETER(int64_t, GC_PAGE_CHECK_NURSERY_LIMIT, "The number of pages to check in the nursery before giving up");
#else
    GC_REGISTER_PARAMETER_DEFAULT(int64_t, GC_PAGE_CHECK_NURSERY_LIMIT, 8);
#endif

#if GC_PAGE_CHECK_GENERAL_LIMIT
    GC_REGISTER_PARAMETER(int64_t, GC_PAGE_CHECK_GENERAL_LIMIT, "The number of pages to check in the general page set before giving up");
#else
    GC_REGISTER_PARAMETER_DEFAULT(int64_t, GC_PAGE_CHECK_GENERAL_LIMIT, 4);
#endif
}

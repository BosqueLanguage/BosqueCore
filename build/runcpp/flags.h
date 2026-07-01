#pragma once

#include "./flagmgr.h"

/**
 * This file contains the flags that are used to enable and disable various features and diagnostics in the runtime. 
 * Also contains GC specific performance flags (nursery size etc.) are in the allocator/flags.h file. 
 **/

namespace ᐸRuntimeᐳ
{
    BSQ_REGISTER_FLAG(RB_INVARIANT_VALIDATE, "Enable red-black tree validation checks");

    GC_REGISTER_FLAG(GC_METRICS, "Enable basic GC metrics collection");

#if GC_NURSERY_BYTES_COLLECT_THRESHOLD
    GC_REGISTER_PARAMETER(int64_t, GC_NURSERY_BYTES_COLLECT_THRESHOLD, "The number of bytes allocated in the nursery before a collection is triggered");
#else
    GC_REGISTER_PARAMETER_DEFAULT(int64_t, GC_NURSERY_BYTES_COLLECT_THRESHOLD, 1ul << 20);
#endif
}

//A bunch of knobs for adjusting GC behavior -- these are all subject to tuning as with the page info above
#define GC_NUM_PAGES_ON_REQ 4
#define GC_DELETE_PENDING_PROCESS_BYTES_COLLECT (GC_NURSERY_BYTES_COLLECT_THRESHOLD / 2)
#define GC_DELETE_PENDING_PROCESS_BYTES_INCREMENTAL (GC_PAGE_SIZE / 2)
//TODO: probably also want to provide dynamic tuning for these rates based on observed backpressure (i.e. how big pending list is)

#define GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC 0.60
#define GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC 0.30
#define GC_PAGE_AVAILABILITY_COUNT_THRESHOLD 8
#define GC_PAGE_CHECK_NURSERY_LIMIT 12
#define GC_PAGE_CHECK_GENERAL_LIMIT 4

//A bunch of flags to turn off/on features
#define GC_CLEAR_EAGER_FEATURE 0
#define GC_MEMORY_CLEAR_FEATURE 0
#define GC_UNIQUE_PARENT_FEATURE 0
#define GC_DETERMINISTIC_ADDRESS_FEATURE 1
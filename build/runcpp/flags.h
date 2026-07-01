#pragma once

/**
 * This file contains the flags that are used to enable and disable various features and diagnostics in the runtime. 
 * Also contains GC specific performance flags (nursery size etc.) are in the allocator/flags.h file. 
 **/

#define BSQ_IF_ENABLED(NAME, OP) if constexpr (NAME) { OP; }
#define GC_IF_ENABLED(NAME, OP) if constexpr (NAME) { OP; }

//Control for page sizes and access
#define GC_BITS_IN_ADDR_FOR_PAGE 12ul
#define GC_PAGE_SIZE (1ul << GC_BITS_IN_ADDR_FOR_PAGE)
#define GC_BLOCK_ALLOCATION_SIZE (1ul << GC_BITS_IN_ADDR_FOR_PAGE)
#define GC_PAGE_MASK ((1ul << GC_BITS_IN_ADDR_FOR_PAGE) - 1ul)
#define GC_PAGE_ADDR_MASK (~GC_PAGE_MASK)

///////////////////////////////////////////////
//Runtime debugging and diagnostics flags

//Enable red-black tree validation checks
#ifndef RB_INVARIANT_VALIDATE
    #define RB_INVARIANT_VALIDATE 0
#endif

///////////////////////////////////////////////
//GC debugging and diagnostics flags

//Process all pages immediately after collection
#ifndef GC_CLEAR_EAGER_FEATURE
    #define GC_CLEAR_EAGER_FEATURE 0
#endif

//Zero out memory when processing pages and RC free
#ifndef GC_MEMORY_CLEAR_FEATURE
    #define GC_MEMORY_CLEAR_FEATURE 0
#endif

//Allow non-deterministic mmap allocations for GC pages
#ifndef GC_ALLOW_NON_DETERMINISTIC_MMAP
    #define GC_ALLOW_NON_DETERMINISTIC_MMAP 0
#endif

///////////////////////////////////////////////
//Feature flags for in progress work

//Enable unique parent tracking for RC objects
#ifndef GC_UNIQUE_PARENT_FEATURE
    #define GC_UNIQUE_PARENT_FEATURE 0
#endif

///////////////////////////////////////////////
//Flags for GC metrics collection and debugging

//Enable basic GC metrics collection
#ifndef GC_METRICS
    #define GC_METRICS 0
#endif

///////////////////////////////////////////////
//Flags for GC performance tuning

//The number of bytes allocated in the nursery before a collection is triggered
#ifndef GC_NURSERY_BYTES_COLLECT_THRESHOLD
    #define GC_NURSERY_BYTES_COLLECT_THRESHOLD (1ul << 20)
#endif

//The number of bytes to process from the pending delete list during a collection
#ifndef GC_DELETE_PENDING_PROCESS_BYTES_COLLECT
    #define GC_DELETE_PENDING_PROCESS_BYTES_COLLECT (GC_NURSERY_BYTES_COLLECT_THRESHOLD / 2)
#endif

//The number of bytes to process from the pending delete list during an incremental get of a new page (if any entries remain)
#ifndef GC_DELETE_PENDING_PROCESS_BYTES_INCREMENTAL
    #define GC_DELETE_PENDING_PROCESS_BYTES_INCREMENTAL (GC_PAGE_SIZE / 2)
#endif

//The number of pages to mmap in from the OS whenever we need new pages
#ifndef GC_NUM_PAGES_ON_REQ
    #define GC_NUM_PAGES_ON_REQ 4
#endif

//The ratio of free slots in a page to consider using it for nursery allocation
#ifndef GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC
    #define GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC 0.60
#endif

//The ratio of free slots in a page to consider it for evacuation allocation
#ifndef GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC
    #define GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC 0.30
#endif

//The number of pages to check in the nursery before giving up and getting one from somewhere else
#ifndef GC_PAGE_CHECK_NURSERY_LIMIT
    #define GC_PAGE_CHECK_NURSERY_LIMIT 8
#endif

//The number of pages to check in the general page set before giving up and getting one from somewhere else
#ifndef GC_PAGE_CHECK_GENERAL_LIMIT
    #define GC_PAGE_CHECK_GENERAL_LIMIT 4
#endif


#pragma once

#include "../common.h"

#define MEM_STATS

#ifdef MEM_STATS

#include <iostream>
#include <chrono>
#include <sstream>
#include <float.h>

// Buckets store BUCKET_VARIANCE us variance, final entry is for outliers (hopefully never any values present there!)
#define MAX_MEMSTATS_BUCKETS 25'000 + 1 /* Might want to make this variant */
#define BUCKET_VARIANCE 2
#define BUCKET_AVERAGE ((BUCKET_VARIANCE) / 2)

typedef double Time;
#define TIME_MAX DBL_MAX
struct Stats {
    size_t count = 0;
    Time mean  = 0.0;
    Time M2    = 0.0;
    Time total = 0.0;
    Time min   = TIME_MAX;
    Time max   = 0.0;
};

struct MemStats {
    size_t total_alloc_count  = 0;
    size_t total_alloc_memory = 0;
    size_t total_live_bytes   = 0;
    size_t total_live_objects = 0;
    size_t total_promotions   = 0;
    size_t total_pages        = 0;

    Stats collection_stats { 0 };
    Stats nursery_stats    { 0 };
    Stats rc_stats         { 0 };

    Time start_time =    0.0; // initialized at creation of mstats object
    Time overhead_time = 0.0; // just to prevent any akward skew in Time for memory intensive programs
    Time total_time =    0.0; // walll clock time (not including mstats compute overhead)

    size_t max_live_heap = 0;

    size_t collection_times[MAX_MEMSTATS_BUCKETS];
    size_t nursery_times[MAX_MEMSTATS_BUCKETS];
    size_t rc_times[MAX_MEMSTATS_BUCKETS];

    MemStats() {
        auto now = std::chrono::high_resolution_clock::now();
        std::chrono::duration<Time, std::micro> dur = now.time_since_epoch();
        this->start_time = dur.count();
    }        
};
extern MemStats g_memstats;

enum class Phase {
    Collection,
    Nursery,
    RC_Old
};

void updateTotalTime();
void printPerfHeader();
void perfDump(Phase p);
void statisticsDump();
void update_bucket(size_t* bucket, double time) noexcept;
std::string generate_formatted_memstats(MemStats& ms) noexcept;
void update_collection_stats(MemStats& ms, double time) noexcept;
void update_nursery_stats(MemStats& ms, double time) noexcept;
void update_rc_stats(MemStats& ms, double time) noexcept;

#define TOTAL_ALLOC_COUNT()      g_memstats.total_alloc_count
#define TOTAL_ALLOC_MEMORY()     g_memstats.total_alloc_memory
#define TOTAL_LIVE_BYTES()       g_memstats.total_live_bytes
#define TOTAL_LIVE_OBJECTS()     g_memstats.total_live_objects
#define TOTAL_PROMOTIONS()       g_memstats.total_promotions
#define TOTAL_PAGES()            g_memstats.total_pages
#define MIN_COLLECTION_TIME()    g_memstats.min_collection_time
#define MAX_COLLECTION_TIME()    g_memstats.max_collection_time
#define MAX_LIVE_HEAP()          g_memstats.max_live_heap

#define UPDATE_TOTAL_ALLOC_COUNT(OP, ...)      TOTAL_ALLOC_COUNT() OP __VA_ARGS__
#define UPDATE_TOTAL_ALLOC_MEMORY(OP, ...)     TOTAL_ALLOC_MEMORY() OP __VA_ARGS__
#define UPDATE_TOTAL_LIVE_BYTES(OP, ...)       TOTAL_LIVE_BYTES() OP __VA_ARGS__
#define UPDATE_TOTAL_LIVE_OBJECTS(OP, ...)     TOTAL_LIVE_OBJECTS() OP __VA_ARGS__
#define UPDATE_TOTAL_PROMOTIONS(OP, ...)       TOTAL_PROMOTIONS() OP __VA_ARGS__
#define UPDATE_TOTAL_PAGES(OP, ...)            TOTAL_PAGES() OP __VA_ARGS__ 
#define UPDATE_MIN_COLLECTION_TIME(OP, ...)    MIN_COLLECTION_TIME() OP __VA_ARGS__
#define UPDATE_MAX_COLLECTION_TIME(OP, ...)    MAX_COLLECTION_TIME() OP __VA_ARGS__
#define UPDATE_MAX_LIVE_HEAP(OP, ...)          MAX_LIVE_HEAP() OP __VA_ARGS__

#define MEM_STATS_DUMP() \
    do { \
        updateTotalTime(); \
        printPerfHeader(); \
        perfDump(Phase::Collection); \
        perfDump(Phase::Nursery); \
        perfDump(Phase::RC_Old); \
        statisticsDump(); \
    } while(0)

#define TIME(T) std::chrono::duration_cast<std::chrono::duration<Time, std::micro>>(T).count()

#define MEM_STATS_START(NAME) \
    auto start_##NAME = std::chrono::high_resolution_clock::now()

#define MEM_STATS_END(BUCKETS, NAME) \
    auto end_##NAME = std::chrono::high_resolution_clock::now(); \
    Time NAME##_ms = TIME(end_##NAME - start_##NAME); \
    update_bucket(g_memstats. BUCKETS, NAME##_ms);

#define COLLECTION_STATS_START() \
    MEM_STATS_START(collection)
#define COLLECTION_STATS_END(BUCKETS) \
    MEM_STATS_END(BUCKETS, collection)

#define NURSERY_STATS_START() \
    MEM_STATS_START(nursery)
#define NURSERY_STATS_END(BUCKETS) \
    MEM_STATS_END(BUCKETS, nursery)

#define RC_STATS_START() \
    MEM_STATS_START(rc)
#define RC_STATS_END(BUCKETS) \
    MEM_STATS_END(BUCKETS, rc)

#define UPDATE_NURSERY_TIMES() \
    update_nursery_stats(g_memstats, nursery_ms)
#define UPDATE_RC_TIMES() \
    update_rc_stats(g_memstats, rc_ms)
#define UPDATE_COLLECTION_TIMES() \
    update_collection_stats(g_memstats, collection_ms)

#define UPDATE_ALLOC_STATS(ALLOC, MEMORY_SIZE) \
    (ALLOC)->updateAllocInfo(MEMORY_SIZE)
    
#define RESET_ALLOC_STATS(ALLOC)   \
    do {                           \
        (ALLOC)->alloc_count = 0;  \
        (ALLOC)->alloc_memory = 0; \
    } while(0)

#define GET_ALLOC_COUNT(ALLOC)  ((ALLOC)->alloc_count)
#define GET_ALLOC_MEMORY(ALLOC) ((ALLOC)->alloc_memory)

#define UPDATE_MEMSTATS_TOTALS(INFO) \
    do { \
        auto mstats_compute_start = std::chrono::high_resolution_clock::now(); \
        UPDATE_NURSERY_TIMES(); \
        UPDATE_RC_TIMES(); \
        UPDATE_COLLECTION_TIMES(); \
        for(size_t i = 0; i < BSQ_MAX_ALLOC_SLOTS; i++) { \
            GCAllocator* alloc = (INFO).g_gcallocs[i]; \
            if(alloc != nullptr) { \
                alloc->updateMemStats(); \
            } \
        } \
        auto mstats_compute_end = std::chrono::high_resolution_clock::now(); \
        Time mstats_compute_elapsed = TIME(mstats_compute_end - mstats_compute_start); \
        g_memstats.overhead_time += mstats_compute_elapsed; \
    } while(0)
#else
struct MemStats {};
#define UPDATE_TOTAL_ALLOC_COUNT(OP, ...)
#define UPDATE_TOTAL_ALLOC_MEMORY(OP, ...)
#define UPDATE_TOTAL_LIVE_BYTES(OP, ...)
#define UPDATE_TOTAL_PROMOTIONS(OP, ...)
#define UPDATE_TOTAL_PAGES(OP, ...)
#define UPDATE_MIN_COLLECTION_TIME(OP, ...)
#define UPDATE_MAX_COLLECTION_TIME(OP, ...)
#define UPDATE_MAX_LIVE_HEAP(OP, ...)

#define update_bucket (void)sizeof
#define compute_average_time(B) 0
#define generate_formatted_memstats(MS) ""
#define MEM_STATS_DUMP()

#define MEM_STATS_START(NAME)
#define MEM_STATS_END(BUCKETS, NAME)

#define COLLECTION_STATS_START()
#define COLLECTION_STATS_END(BUCKETS)

#define NURSERY_STATS_START()
#define NURSERY_STATS_END(BUCKETS)

#define RC_STATS_START()
#define RC_STATS_END(BUCKETS)

#define UPDATE_COLLECTION_TIMES()
#define UPDATE_NURSERY_TIMES()
#define UPDATE_RC_TIMES()
#define UPDATE_MEMSTATS_TOTALS(INFO)

#define UPDATE_ALLOC_STATS(ALLOC, MEMORY_SIZE)
#define RESET_ALLOC_STATS(ALLOC)
#define GET_ALLOC_COUNT(ALLOC) (0)
#define GET_ALLOC_MEMORY(ALLOC) (0)

#endif// MEM_STATS

#pragma once

#include "../common.h"

#ifdef MEM_STATS

#include <iostream>
#include <chrono>
#include <sstream>
#include <float.h>

// Buckets store BUCKET_VARIANCE us variance, final entry is for outliers (hopefully never any values present there!)
#define MAX_MEMSTATS_BUCKETS 25'000 + 1 /* Might want to make this variant */
#define BUCKET_VARIANCE 2
#define BUCKET_AVERAGE ((BUCKET_VARIANCE) / 2)

enum class Phase {
	Collection,
	Nursery,
	RC_Old
};

typedef double Time;
#define TIME_MAX DBL_MAX
#define TIMES_LIST_SIZE 500

struct Stats {
    size_t count = 0;
    Time mean  = 0.0;
    Time M2    = 0.0;
    Time total = 0.0;
    Time min   = TIME_MAX;
    Time max   = 0.0;

	void update(double t) noexcept;
};

struct MemStats {
    size_t total_alloc_count  = 0;
    size_t total_alloc_memory = 0;
    size_t total_live_bytes   = 0;
    size_t total_live_objects = 0;
    size_t total_promotions   = 0;
    size_t total_pages        = 0;

    Stats collection_stats = {0};
    Stats nursery_stats = {0};
    Stats rc_stats = {0};

	// Not of use to the global memstats, just easier to leave it present
	size_t times_count = 0;	
	Time collection_times[TIMES_LIST_SIZE];
	Time nursery_times[TIMES_LIST_SIZE];
	Time rc_times[TIMES_LIST_SIZE];

    Time start_time =    0.0; // initialized at creation of mstats object
    Time overhead_time = 0.0; // just to prevent any akward skew in Time for memory intensive programs
    Time total_time =    0.0; // wall clock time (not including mstats compute overhead)

    size_t max_live_heap = 0;

	// Each bucket is a counter for how many times a collection/nursery/rc phase's
	// time was in this buckets range
    size_t collection_buckets[MAX_MEMSTATS_BUCKETS];
    size_t nursery_buckets[MAX_MEMSTATS_BUCKETS];
    size_t rc_buckets[MAX_MEMSTATS_BUCKETS];

    MemStats() {
        auto now = std::chrono::high_resolution_clock::now();
        std::chrono::duration<Time, std::micro> dur = now.time_since_epoch();
        this->start_time = dur.count();
    }        

	void updateTotalTime();
	void printPerfHeader();
	void perfDump(Phase p);
	void statisticsDump();
	std::string generateFormattedMemstats() noexcept;
	void updateTelemetry(Phase p, double t) noexcept;
	void processAllTimesLists(MemStats& src, const size_t ntimes) noexcept;
	void mergeNonTimeLists(MemStats& src);
	void tryMergeTimesLists(MemStats& src, bool force) noexcept;

	// Automatically called at the destruction of a thread
	void merge(MemStats& src);
};
extern MemStats g_memstats;

#define TOTAL_ALLOC_COUNT(MS)      (MS).total_alloc_count
#define TOTAL_ALLOC_MEMORY(MS)     (MS).total_alloc_memory
#define TOTAL_LIVE_BYTES(MS)       (MS).total_live_bytes
#define TOTAL_LIVE_OBJECTS(MS)     (MS).total_live_objects
#define TOTAL_PROMOTIONS(MS)       (MS).total_promotions
#define TOTAL_PAGES(MS)            (MS).total_pages
#define MIN_COLLECTION_TIME(MS)    (MS).min_collection_time
#define MAX_COLLECTION_TIME(MS)    (MS).max_collection_time
#define MAX_LIVE_HEAP(MS)          (MS).max_live_heap

#define UPDATE_TOTAL_ALLOC_COUNT(MS, OP, ...) \
	TOTAL_ALLOC_COUNT(MS) OP __VA_ARGS__
#define UPDATE_TOTAL_ALLOC_MEMORY(MS, OP, ...) \
	TOTAL_ALLOC_MEMORY(MS) OP __VA_ARGS__
#define UPDATE_TOTAL_LIVE_BYTES(MS, OP, ...) \
	TOTAL_LIVE_BYTES(MS) OP __VA_ARGS__
#define UPDATE_TOTAL_LIVE_OBJECTS(MS, OP, ...) \
	TOTAL_LIVE_OBJECTS(MS) OP __VA_ARGS__
#define UPDATE_TOTAL_PROMOTIONS(MS, OP, ...) \
	TOTAL_PROMOTIONS(MS) OP __VA_ARGS__
#define UPDATE_TOTAL_PAGES(MS, OP, ...) \
	TOTAL_PAGES(MS) OP __VA_ARGS__ 
#define UPDATE_MIN_COLLECTION_TIME(MS, OP, ...) \
	MIN_COLLECTION_TIME(MS) OP __VA_ARGS__
#define UPDATE_MAX_COLLECTION_TIME(MS, OP, ...) \
	MAX_COLLECTION_TIME(MS) OP __VA_ARGS__
#define UPDATE_MAX_LIVE_HEAP(MS, OP, ...) \
	MAX_LIVE_HEAP(MS) OP __VA_ARGS__

#define MEM_STATS_DUMP(MS) \
    do { \
        (MS).updateTotalTime(); \
        (MS).printPerfHeader(); \
        (MS).perfDump(Phase::Collection); \
        (MS).perfDump(Phase::Nursery); \
        (MS).perfDump(Phase::RC_Old); \
        (MS).statisticsDump(); \
    } while(0)

#define MEM_STATS_PRINT(S) std::cout << S

#define TIME(T) \
	std::chrono::duration_cast<std::chrono::duration<Time, std::micro>>(T).count()

#define MEM_STATS_START(PHASE) \
    auto start_##PHASE = std::chrono::high_resolution_clock::now()

#define MEM_STATS_END(PHASE, MS) \
    auto end_##PHASE = std::chrono::high_resolution_clock::now(); \
    Time PHASE##_ms = TIME(end_##PHASE - start_##PHASE); \
    (MS).updateTelemetry(Phase:: PHASE, PHASE##_ms);

#define UPDATE_ALLOC_STATS(ALLOC, MEMORY_SIZE) \
    (ALLOC)->updateAllocInfo(MEMORY_SIZE)
    
#define RESET_ALLOC_STATS(ALLOC)   \
    do {                           \
        (ALLOC)->alloc_count = 0;  \
        (ALLOC)->alloc_memory = 0; \
    } while(0)

#define GET_ALLOC_COUNT(ALLOC)  ((ALLOC)->alloc_count)
#define GET_ALLOC_MEMORY(ALLOC) ((ALLOC)->alloc_memory)

// TODO pretty sure we need to revisit how we compute the overheads here
#define UPDATE_MEMSTATS_TOTALS(INFO) \
    do { \
        auto mstats_compute_start = std::chrono::high_resolution_clock::now(); \
        for(size_t i = 0; i < BSQ_MAX_ALLOC_SLOTS; i++) { \
            GCAllocator* alloc = (INFO).g_gcallocs[i]; \
            if(alloc != nullptr) { \
                alloc->updateMemStats(); \
            } \
        } \
		{\
			std::lock_guard ms_lk(g_gctelemetrylock);\
			g_memstats.tryMergeTimesLists((INFO).memstats, false); \
		}\
        auto mstats_compute_end = std::chrono::high_resolution_clock::now(); \
        Time mstats_compute_elapsed = TIME(mstats_compute_end - mstats_compute_start); \
        (INFO).memstats.overhead_time += mstats_compute_elapsed; \
    } while(0)

#define MERGE_MEMSTATS(MS) g_memstats.merge(MS)

#else

#define UPDATE_TOTAL_ALLOC_COUNT(MS, OP, ...)
#define UPDATE_TOTAL_ALLOC_MEMORY(MS, OP, ...)
#define UPDATE_TOTAL_LIVE_BYTES(MS, OP, ...)
#define UPDATE_TOTAL_LIVE_OBJECTS(MS, OP, ...)
#define UPDATE_TOTAL_PROMOTIONS(MS, OP, ...)
#define UPDATE_TOTAL_PAGES(MS, OP, ...)
#define UPDATE_MAX_LIVE_HEAP(MS, OP, ...)

#define MEM_STATS_DUMP(MS)
#define MEM_STATS_PRINT(S)

#define MEM_STATS_START(NAME)
#define MEM_STATS_END(PHASE, MS)

#define UPDATE_MEMSTATS_TOTALS(INFO)

#define UPDATE_ALLOC_STATS(ALLOC, MEMORY_SIZE)

#define MERGE_MEMSTATS(MS)

#endif // MEM_STATS

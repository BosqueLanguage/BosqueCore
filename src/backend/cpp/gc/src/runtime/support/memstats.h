#pragma once

#include "../common.h"

#define MEM_STATS

#ifdef MEM_STATS

#include <iostream>
#include <chrono>

// Buckets store BUCKET_VARIANCE ms variance, final entry is for outliers (hopefully never any values present there!)
#define MAX_MEMSTATS_BUCKETS 10000 + 1
#define BUCKET_VARIANCE 0.001
#define BUCKET_AVERAGE ((BUCKET_VARIANCE) / 2)

struct Stats {
    size_t count = 0;
    double mean  = 0.0;
    double M2    = 0.0;
    double total = 0.0;
};

struct MemStats {
    size_t total_alloc_count  = 0;
    size_t prev_total_alloc_count = 0;
    size_t total_alloc_memory = 0;
    size_t total_live_bytes   = 0;
    size_t total_live_objects = 0;
    size_t total_promotions   = 0;
    size_t total_pages        = 0;

    Stats collection_stats { 0 };
    Stats nursery_stats    { 0 };
    Stats rc_stats         { 0 };

    double start_time = 0.0;
    double total_time = 0.0;

    double survival_rate_sum = 0.0;

    double min_collection_time = 0;
    double max_collection_time = 0;

    size_t max_live_heap = 0;

    size_t collection_times[MAX_MEMSTATS_BUCKETS] { 0 };
    size_t nursery_times[MAX_MEMSTATS_BUCKETS]    { 0 };
    size_t rc_times[MAX_MEMSTATS_BUCKETS]         { 0 };

    MemStats() {
        auto start = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> dur = start.time_since_epoch();
        this->start_time = dur.count();
    }        
};

extern MemStats g_memstats;

#define COLLECTION_STATS_MODE
#define NURSERY_RC_STATS_MODE

#define TOTAL_ALLOC_COUNT()      g_memstats.total_alloc_count
#define PREV_TOTAL_ALLOC_COUNT() g_memstats.prev_total_alloc_count
#define TOTAL_ALLOC_MEMORY()     g_memstats.total_alloc_memory
#define TOTAL_LIVE_BYTES()       g_memstats.total_live_bytes
#define TOTAL_LIVE_OBJECTS()     g_memstats.total_live_objects
#define TOTAL_PROMOTIONS()       g_memstats.total_promotions
#define TOTAL_PAGES()            g_memstats.total_pages
#define MIN_COLLECTION_TIME()    g_memstats.min_collection_time
#define MAX_COLLECTION_TIME()    g_memstats.max_collection_time
#define MAX_LIVE_HEAP()          g_memstats.max_live_heap

#define UPDATE_TOTAL_ALLOC_COUNT(OP, ...)      TOTAL_ALLOC_COUNT() OP __VA_ARGS__
#define UPDATE_PREV_TOTAL_ALLOC_COUNT()        PREV_TOTAL_ALLOC_COUNT() = TOTAL_ALLOC_COUNT()
#define UPDATE_TOTAL_ALLOC_MEMORY(OP, ...)     TOTAL_ALLOC_MEMORY() OP __VA_ARGS__
#define UPDATE_TOTAL_LIVE_BYTES(OP, ...)       TOTAL_LIVE_BYTES() OP __VA_ARGS__
#define UPDATE_TOTAL_LIVE_OBJECTS(OP, ...)     TOTAL_LIVE_OBJECTS() OP __VA_ARGS__
#define UPDATE_TOTAL_PROMOTIONS(OP, ...)       TOTAL_PROMOTIONS() OP __VA_ARGS__
#define UPDATE_TOTAL_PAGES(OP, ...)            TOTAL_PAGES() OP __VA_ARGS__ 
#define UPDATE_MIN_COLLECTION_TIME(OP, ...)    MIN_COLLECTION_TIME() OP __VA_ARGS__
#define UPDATE_MAX_COLLECTION_TIME(OP, ...)    MAX_COLLECTION_TIME() OP __VA_ARGS__
#define UPDATE_MAX_LIVE_HEAP(OP, ...)          MAX_LIVE_HEAP() OP __VA_ARGS__

void update_stats(Stats& stats, double time) noexcept;
void update_bucket(size_t* bucket, double time) noexcept;
double get_mean_pause(Stats& stats) noexcept;
double get_stddev(const Stats& stats) noexcept;
std::string generate_formatted_memstats(MemStats& ms) noexcept;
double calculate_percentile_from_buckets(const size_t* buckets, double percentile) noexcept;
void update_collection_extrema(MemStats& ms, double time) noexcept;
void update_collection_stats(MemStats& ms, double time) noexcept;
void update_nursery_stats(MemStats& ms, double time) noexcept;
void update_rc_stats(MemStats& ms, double time) noexcept;
void update_survival_rate_sum(MemStats& ms) noexcept;
double calculate_total_collection_time(const size_t* buckets) noexcept;

#define MEM_STATS_START(NAME) \
    auto start_##NAME = std::chrono::high_resolution_clock::now()

#define MEM_STATS_END(BUCKETS, NAME) \
    auto end_##NAME = std::chrono::high_resolution_clock::now(); \
    double NAME##_ms = std::chrono::duration_cast<std::chrono::duration<double, std::milli>>(end_##NAME - start_##NAME).count(); \
    update_bucket(g_memstats. BUCKETS, NAME##_ms);

#ifdef COLLECTION_STATS_MODE

#define COLLECTION_STATS_START() \
    MEM_STATS_START(collection)
#define COLLECTION_STATS_END(BUCKETS) \
    MEM_STATS_END(BUCKETS, collection)

#define UPDATE_COLLECTION_TIMES() \
    update_collection_stats(g_memstats, collection_ms)

#define NURSERY_STATS_START()
#define NURSERY_STATS_END(BUCKETS)
#define RC_STATS_START()

#define RC_STATS_END(BUCKETS)
#define UPDATE_NURSERY_TIMES() 

#define UPDATE_RC_TIMES()

#elif defined(NURSERY_RC_STATS_MODE) 

#define UPDATE_COLLECTION_TIMES()
#define COLLECTION_STATS_START()
#define COLLECTION_STATS_END(BUCKETS)

#define NURSERY_STATS_START() \
    MEM_STATS_START(nursery)
#define NURSERY_STATS_END(BUCKETS) \
    MEM_STATS_END(INFO, BUCKETS, nursery)

#define RC_STATS_START() \
    MEM_STATS_START(rc)
#define RC_STATS_END(BUCKETS) \
    MEM_STATS_END(BUCKETS, rc)

#define UPDATE_NURSERY_TIMES() \
    update_nursery_stats(g_memstats, nursery_ms)
#define UPDATE_RC_TIMES() \
    update_rc_stats(g_memstats, rc_ms)
#else
#define UPDATE_COLLECTION_TIMES()
#define UPDATE_NURSERY_TIMES()
#define UPDATE_RC_TIMES()
#endif

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
        auto now = std::chrono::high_resolution_clock::now(); \
        g_memstats.total_time = std::chrono:: \
            duration_cast<std::chrono::duration<double, std::milli>> \
            (now.time_since_epoch()).count() - g_memstats.start_time; \
        for(size_t i = 0; i < BSQ_MAX_ALLOC_SLOTS; i++) { \
            GCAllocator* alloc = (INFO).g_gcallocs[i]; \
            if(alloc != nullptr) { \
                alloc->updateMemStats(); \
            } \
        } \
        update_survival_rate_sum(g_memstats); \
        UPDATE_PREV_TOTAL_ALLOC_COUNT(); \
    } while(0)

#define PRINT_COLLECTION_TIME() \
    do{ \
        double mean = get_mean_pause(g_memstats.collection_stats); \
        double stddev = get_stddev(g_memstats.collection_stats); \
        std::cout << "Collection Average: " << mean << "ms\n"; \
        std::cout << "Collection Std Dev: " << stddev << "ms\n"; \
        std::cout << "Collection 1σ:      " << stddev << "ms\n"; \
        std::cout << "Collection 2σ:      " << (2 * stddev) << "ms\n"; \
        std::cout << "Collection Min:     " << g_memstats.min_collection_time << "ms\n"; \
        std::cout << "Collection Max:     " << g_memstats.max_collection_time << "ms\n"; \
        std::cout << "Collection 50th:    " << calculate_percentile_from_buckets(g_memstats.collection_times, 0.50) << "ms\n"; \
        std::cout << "Collection 95th:    " << calculate_percentile_from_buckets(g_memstats.collection_times, 0.95) << "ms\n"; \
        std::cout << "Collection 99th:    " << calculate_percentile_from_buckets(g_memstats.collection_times, 0.99) << "ms\n"; \
    } while(0)
#define PRINT_TOTAL_COLLECTIONS() \
    std::cout << "Total Collections: " << g_memstats.collection_stats.count << "\n"

#define PRINT_NURSERY_TIME() \
    std::cout << "Nursery Average: " << get_mean_pause(g_memstats.nursery_stats) << "ms\n"

#define PRINT_RC_TIME() \
    std::cout << "RC Average: " << get_mean_pause(g_memstats.rc_stats) << "ms\n"

#define PRINT_TOTAL_PAGES() \
    std::cout << "Total Pages: " << g_memstats.total_pages << "\n"

#define PRINT_HEAP_SIZE() \
    std::cout << "Heap Size: " << g_memstats.total_pages * BSQ_BLOCK_ALLOCATION_SIZE << " bytes\n"

#define PRINT_ALLOC_INFO()                                                                     \
    do {                                                                                        \
        std::cout << "Total Alloc Count: " << g_memstats.total_alloc_count << "\n";             \
        std::cout << "Total Allocated Memory: " << g_memstats.total_alloc_memory << " bytes\n"; \
    } while(0)

#define PRINT_TOTAL_PROMOTIONS() \
    std::cout << "Total Promotions: " << g_memstats.total_promotions << "\n"

#define PRINT_MAX_HEAP() \
    std::cout << "Max Live Heap Size: " << g_memstats.max_live_heap << " bytes\n"

// Both wrong, they include time to compute memstats (at end of collection) so they are forcefully skewed
#define PRINT_TOTAL_TIME() \
    do {\
        std::cout << "Total Time: " << g_memstats.total_time << "ms\n"; \
        std::cout << "Percentage of Time Collecting: " << (calculate_total_collection_time(g_memstats.collection_times) / g_memstats.total_time) * 100.0 << "%\n";\
    } while(0)

#define PRINT_SURVIVAL_RATE() \
    std::cout << "Survival Rate: " << (g_memstats.total_promotions / g_memstats.total_alloc_count) * 100.0 << "%\n";

#define MEM_STATS_DUMP() \
    do { \
        PRINT_COLLECTION_TIME(); \
        PRINT_NURSERY_TIME(); \
        PRINT_RC_TIME(); \
        PRINT_TOTAL_TIME(); \
        PRINT_TOTAL_COLLECTIONS(); \
        PRINT_TOTAL_PROMOTIONS(); \
        PRINT_ALLOC_INFO(); \
        PRINT_TOTAL_PAGES(); \
        PRINT_MAX_HEAP(); \
        PRINT_HEAP_SIZE(); \
        PRINT_SURVIVAL_RATE(); \
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
#define MEM_STATS_END(INFO, BUCKETS, NAME)

#define COLLECTION_STATS_START()
#define COLLECTION_STATS_END(INFO, BUCKETS)

#define NURSERY_STATS_START()
#define NURSERY_STATS_END(INFO, BUCKETS)

#define RC_STATS_START()
#define RC_STATS_END(INFO, BUCKETS)

#define UPDATE_COLLECTION_TIMES(INFO)
#define UPDATE_NURSERY_TIMES(INFO)
#define UPDATE_RC_TIMES(INFO)
#define UPDATE_MEMSTATS_TOTALS(INFO)

#define UPDATE_ALLOC_STATS(ALLOC, MEMORY_SIZE)
#define RESET_ALLOC_STATS(ALLOC)
#define GET_ALLOC_COUNT(ALLOC) (0)
#define GET_ALLOC_MEMORY(ALLOC) (0)

#endif// MEM_STATS
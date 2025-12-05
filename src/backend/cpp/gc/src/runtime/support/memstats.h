#pragma once

#include "../common.h"

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
};

inline void update_bucket(size_t* bucket, double time) noexcept 
{
    int index = static_cast<int>((time * (1.0 / BUCKET_VARIANCE)) + 0.5);
    if(index >= MAX_MEMSTATS_BUCKETS) { 
        bucket[MAX_MEMSTATS_BUCKETS - 1]++;
    }
    else {
        bucket[index]++;
    }
}

void update_stats(Stats& stats, double time) noexcept;
double get_mean_pause(Stats& stats) noexcept;
double get_stddev(const Stats& stats) noexcept;

std::string generate_formatted_memstats(MemStats& ms) noexcept;

inline double calculate_percentile_from_buckets(const size_t* buckets, double percentile) noexcept 
{
    size_t total = 0;
    for (int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        total += buckets[i];
    }
    
    if (total == 0) {
        return 0.0;
    }
    
    size_t target_count = static_cast<size_t>(total * percentile);
    size_t cumulative = 0;
    
    for (int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        cumulative += buckets[i];
        if (cumulative >= target_count) {
            return i * BUCKET_VARIANCE;
        }
    }
    
    return (MAX_MEMSTATS_BUCKETS - 1) * BUCKET_VARIANCE;
}

inline void update_collection_extrema(MemStats& ms, double time) noexcept 
{
    if(time > ms.max_collection_time) { 
        ms.max_collection_time = time;  
    }
    if(time < ms.min_collection_time || ms.min_collection_time < 1e-10) { 
        ms.min_collection_time = time;
    }
}

inline void update_collection_stats(MemStats& ms, double time) noexcept 
{
    update_collection_extrema(ms, time);
    update_stats(ms.collection_stats, time);
}

inline void update_nursery_stats(MemStats& ms, double time) noexcept 
{
    update_stats(ms.nursery_stats, time);
}

inline void update_rc_stats(MemStats& ms, double time) noexcept 
{
    update_stats(ms.rc_stats, time);
}

inline void update_survival_rate_sum(MemStats& ms) noexcept 
{
    ms.survival_rate_sum += static_cast<double>(ms.total_live_objects) / static_cast<double>(ms.total_alloc_count - ms.prev_total_alloc_count);
}

inline double calculate_total_collection_time(const size_t* buckets) noexcept
{
    double curvariance = BUCKET_VARIANCE;
    double total = 0.0;
    for (int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        total += buckets[i] * curvariance;
        curvariance += BUCKET_VARIANCE;
    }

    return total;
}

#define PRINT_COLLECTION_TIME(E) \
    do{ \
        double mean = get_mean_pause((E).mstats.collection_stats); \
        double stddev = get_stddev((E).mstats.collection_stats); \
        std::cout << "Collection Average: " << mean << "ms\n"; \
        std::cout << "Collection Std Dev: " << stddev << "ms\n"; \
        std::cout << "Collection 1σ: " << stddev << "ms\n"; \
        std::cout << "Collection 2σ: " << (2 * stddev) << "ms\n"; \
        std::cout << "Collection Min: " << (E).mstats.min_collection_time << "ms\n"; \
        std::cout << "Collection Max: " << (E).mstats.max_collection_time << "ms\n"; \
        std::cout << "Collection 50th: " << calculate_percentile_from_buckets((E).mstats.collection_times, 0.50) << "ms\n"; \
        std::cout << "Collection 95th: " << calculate_percentile_from_buckets((E).mstats.collection_times, 0.95) << "ms\n"; \
        std::cout << "Collection 99th: " << calculate_percentile_from_buckets((E).mstats.collection_times, 0.99) << "ms\n"; \
    } while(0)
#define PRINT_TOTAL_COLLECTIONS(E) \
    (std::cout << "Total Collections: " << (E).mstats.collection_stats.count << "\n")

#define PRINT_NURSERY_TIME(E) \
        std::cout << "Nursery Average: " << get_mean_pause((E).mstats.nursery_stats) << "ms\n";

#define PRINT_RC_TIME(E) \
    std::cout << "RC Average: " << get_mean_pause((E).mstats.rc_stats) << "ms\n";

#define PRINT_TOTAL_PAGES(E) \
    (std::cout << "Total Pages: " << (E).mstats.total_pages << "\n")

#define PRINT_HEAP_SIZE(E) \
    (std::cout << "Heap Size: " << (E).mstats.total_pages * BSQ_BLOCK_ALLOCATION_SIZE << " bytes\n")

#define PRINT_ALLOC_INFO(E)                                                                     \
    do {                                                                                        \
        std::cout << "Total Alloc Count: " << (E).mstats.total_alloc_count << "\n";             \
        std::cout << "Total Allocated Memory: " << (E).mstats.total_alloc_memory << " bytes\n"; \
    } while(0)

#define PRINT_TOTAL_PROMOTIONS(E) \
    (std::cout << "Total Promotions: " << (E).mstats.total_promotions << "\n")

#define PRINT_MAX_HEAP(E) \
    (std::cout << "Max Live Heap Size: " << (E).mstats.max_live_heap << " bytes\n")

#define PRINT_TOTAL_TIME(E) \
    do {\
        (E).mstats.total_time -= (E).mstats.start_time; \
        std::cout << "Total Time: " << (E).mstats.total_time << "ms\n"; \
        std::cout << "Percentage of Time Collecting: " << (calculate_total_collection_time((E).mstats.collection_times) / (E).mstats.total_time) * 100.0 << "%\n";\
    } while(0)

#define PRINT_SURVIVAL_RATE(E) \
    std::cout << "Survival Rate: " << ((E).mstats.survival_rate_sum / static_cast<double>((E).mstats.collection_stats.count)) * 100.0 << "%\n";

#define MEM_STATS_DUMP(E) \
    do { \
        PRINT_COLLECTION_TIME(E); \
        PRINT_NURSERY_TIME(E); \
        PRINT_RC_TIME(E); \
        PRINT_TOTAL_TIME(E); \
        PRINT_TOTAL_COLLECTIONS(E); \
        PRINT_TOTAL_PROMOTIONS(E); \
        PRINT_ALLOC_INFO(E); \
        PRINT_TOTAL_PAGES(E); \
        PRINT_MAX_HEAP(E); \
        PRINT_HEAP_SIZE(E); \
        PRINT_SURVIVAL_RATE(E); \
    } while(0)

#else
struct MemStats {};
#define update_bucket (void)sizeof
#define compute_average_time(B) 0
#define generate_formatted_memstats(MS) ""
#define MEM_STATS_DUMP(E)

#endif// MEM_STATS
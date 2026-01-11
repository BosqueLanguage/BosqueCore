#include "memstats.h"

#ifdef MEM_STATS

#include <cmath>

MemStats g_memstats;

void statistics_dump()
{
    std::stringstream ss;
    ss  << "Statistics:\n"
        << "\tTotal Time        " << g_memstats.total_time << "ms\n"
        << "\tTotal Collections " << g_memstats.collection_stats.count << std::endl
        << "\tTime Collecting   " << (calculate_total_collection_time(g_memstats.collection_times) / g_memstats.total_time) * 100.0 << "%\n"
        << "\tTotal Pages       " << g_memstats.total_pages << std::endl
        << "\tMax Live Heap     " << g_memstats.max_live_heap << "b\n"
        << "\tHeap Size         " << g_memstats.total_pages * BSQ_BLOCK_ALLOCATION_SIZE << "b\n"
        << "\tAlloc Count       " << g_memstats.total_alloc_count << std::endl
        << "\tAlloc'd Memory    " << g_memstats.total_alloc_memory << "b\n"
        << "\tSurvival Rate     " << ((double)g_memstats.total_promotions / (double)g_memstats.total_alloc_count) * 100.0 << "%\n";

    std::cout << ss.str();
}

void update_stats(Stats& stats, double time) noexcept
{
    // Welford's algorithm
    stats.count++;
    double delta = time - stats.mean;
    stats.mean += delta / stats.count;
    double delta2 = time - stats.mean;
    stats.M2 += delta * delta2;
}

void update_bucket(size_t* bucket, double time) noexcept 
{
    int index = static_cast<int>((time * (1.0 / BUCKET_VARIANCE)) + 0.5);
    if(index >= MAX_MEMSTATS_BUCKETS) { 
        bucket[MAX_MEMSTATS_BUCKETS - 1]++;
    }
    else {
        bucket[index]++;
    }
}

double get_mean_pause(Stats& stats) noexcept
{
    return stats.mean;
}

double get_stddev(const Stats& stats) noexcept 
{
    if(stats.count < 2) {
        return 0.0;
    }

    return std::sqrt(stats.M2 / stats.count);
}

double calculate_percentile_from_buckets(const size_t* buckets, double percentile) noexcept 
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

void update_collection_extrema(MemStats& ms, double time) noexcept 
{
    if(time > ms.max_collection_time) { 
        ms.max_collection_time = time;  
    }
    if(time < ms.min_collection_time || ms.min_collection_time < 1e-10) { 
        ms.min_collection_time = time;
    }
}

void update_collection_stats(MemStats& ms, double time) noexcept 
{
    update_collection_extrema(ms, time);
    update_stats(ms.collection_stats, time);
}

void update_nursery_stats(MemStats& ms, double time) noexcept 
{
    update_stats(ms.nursery_stats, time);
}

void update_rc_stats(MemStats& ms, double time) noexcept 
{
    update_stats(ms.rc_stats, time);
}

double calculate_total_collection_time(const size_t* buckets) noexcept
{
    double curvariance = BUCKET_VARIANCE;
    double total = 0.0;
    for (int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        total += buckets[i] * curvariance;
        curvariance += BUCKET_VARIANCE;
    }

    return total;
}

std::string generate_bucket_data(size_t buckets[MAX_MEMSTATS_BUCKETS]) noexcept 
{
    std::string buf = "[";
    for(int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        std::string ndata = std::to_string(buckets[i]);
        if(i != MAX_MEMSTATS_BUCKETS - 1) {
            ndata += ", ";
        }
        
        buf += ndata;    
    }
    return buf + "]\n";
}

//
// Spits out contents of each bucket in a format like so: 
// {Bucket Variance, Number of Buckets}
// <Statistic Name>[data, data, data]
// <Statistic Name>[data, data, data] ...
//
std::string generate_formatted_memstats(MemStats& ms) noexcept
{
    std::string header = "{" + std::to_string(BUCKET_VARIANCE) 
        + ", " + std::to_string(MAX_MEMSTATS_BUCKETS) + "}\n";

    std::string collection_data = generate_bucket_data(ms.collection_times);
    std::string collection_times = "<Collection Times>" + collection_data;

    std::string nursery_data = generate_bucket_data(ms.nursery_times);
    std::string nursery_times = "<Nursery Times>" + nursery_data;

    std::string rc_data = generate_bucket_data(ms.rc_times);
    std::string rc_times = "<RC Times>" + rc_data;

    return header + collection_times + nursery_times + rc_times;
}

#endif // MEM_STATS
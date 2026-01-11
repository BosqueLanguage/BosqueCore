#include "memstats.h"

#ifdef MEM_STATS

#include <cmath>
#include <iomanip>

MemStats g_memstats{};

#define RST  "\x1B[0m"
#define BOLD(x)	"\x1B[1m" x RST
#define UNDL(x)	"\x1B[4m" x RST

enum class Unit {
    Count,
    Percentage,
    Microseconds,
    Bytes
};

#define WRITE_UNIT(STREAM, V, UNIT, CNT, SEC, BYTE) \
    do { \
        switch(UNIT) { \
            case Unit::Count: { \
                STREAM << V << CNT; \
                break; \
            } \
            case Unit::Microseconds: { \
                STREAM << V << SEC; \
                break; \
            } \
            case Unit::Bytes: { \
                STREAM << V << BYTE; \
                break; \
            } \
            default: break; \
        } \
    } while(0)

static std::string printUnit(double v, Unit u)
{
    std::stringstream ss;
    if(u == Unit::Percentage) {
        ss << v << "%";
        return ss.str();
    }

    if(v > 1'000'000'000'000.0) {
        v /= 1'000'000'000'000.0;
        WRITE_UNIT(ss, v, u, "T", "Ms", "TB");
    }
    else if(v > 1'000'000'000.0) {
        v /= 1'000'000'000.0;
        WRITE_UNIT(ss, v, u, "G", "ks", "GB");
    }
    else if(v > 1'000'000.0) {
        v /= 1'000'000.0;
        WRITE_UNIT(ss, v, u, "M", "s", "MB");
    }
    else if(v > 1'000.0) {
        v /= 1'000.0;
        WRITE_UNIT(ss, v, u, "K", "ms", "KB");
    }
    else {
        WRITE_UNIT(ss, v, u, " ", "us", "B");
    }

    return ss.str();
}

//
// TODO: Need formatting to 3 sig digs
//

#define WIDTH 12 
#define NAME_WIDTH 15

static void formatPerf(const std::string& phase, Stats& s, size_t* time_buckets)
{
    std::string mean = printUnit(get_mean_pause(s), Unit::Microseconds);
    std::string std_dev = printUnit(get_stddev(s), Unit::Microseconds);
    std::string min = printUnit(s.min, Unit::Microseconds);
    std::string max = printUnit(s.max, Unit::Microseconds);
    std::string fiftyth = printUnit(calculate_percentile_from_buckets(time_buckets, 0.50), Unit::Microseconds);
    std::string ninetyfifth = printUnit(calculate_percentile_from_buckets(time_buckets, 0.95), Unit::Microseconds);
    std::string ninetynineth = printUnit(calculate_percentile_from_buckets(time_buckets, 0.99), Unit::Microseconds);

    std::stringstream ss;
    ss  << std::setw(NAME_WIDTH) << phase
        << std::setw(WIDTH)      << mean 
        << std::setw(WIDTH)      << std_dev
        << std::setw(WIDTH)      << min 
        << std::setw(WIDTH)      << max
        << std::setw(WIDTH)      << fiftyth
        << std::setw(WIDTH)      << ninetyfifth
        << std::setw(WIDTH)      << ninetynineth;

    std::cout << ss.str() << std::endl;
}

void printPerfHeader()
{
    std::stringstream ss;
    ss  << BOLD("Performance:\n") 
        << std::setw(NAME_WIDTH) << "Measurement"
        << std::setw(WIDTH)      << "Mean"
        << std::setw(WIDTH)      << "σ"
        << std::setw(WIDTH)      << "Min"
        << std::setw(WIDTH)      << "Max"
        << std::setw(WIDTH)      << "50% "
        << std::setw(WIDTH)      << "95% "
        << std::setw(WIDTH)      << "99%";

    std::cout << ss.str() << std::endl;
}

void perfDump(Phase p)
{
    switch(p) {
        case Phase::Collection: {
            formatPerf("Collection", g_memstats.collection_stats, g_memstats.collection_times);
            break;
        }
        case Phase::Nursery: {
            formatPerf("Nursery", g_memstats.nursery_stats, g_memstats.nursery_times);
            break;
        }
        case Phase::RC_Old: {
            formatPerf("RC Old", g_memstats.rc_stats, g_memstats.rc_times);           
            break;
        }
        default: break;
    }
}

//
// TODO: These are _better_ but still not quite what we would expect from doing 'time ./output/memex`, so 
// we need to pinpoint the hotspots for memstats computation and adjust accordingly
//
void statisticsDump()
{
    std::stringstream ss;
    ss  << BOLD("Statistics:\n")
        << BOLD("\tTotal Time        ") << printUnit(g_memstats.total_time, Unit::Microseconds) << std::endl 
        << BOLD("\tTime Collecting   ") << printUnit((g_memstats.collection_stats.total / g_memstats.total_time) * 100.0, Unit::Percentage) << std::endl
        << BOLD("\tTotal Collections ") << printUnit(g_memstats.collection_stats.count, Unit::Count) << std::endl
        << BOLD("\tTotal Pages       ") << printUnit(g_memstats.total_pages, Unit::Count) << std::endl
        << BOLD("\tMax Live Heap     ") << printUnit(g_memstats.max_live_heap, Unit::Bytes) << "\n"
        << BOLD("\tHeap Size         ") << printUnit(g_memstats.total_pages * BSQ_BLOCK_ALLOCATION_SIZE, Unit::Bytes) << "\n"
        << BOLD("\tAlloc Count       ") << printUnit(g_memstats.total_alloc_count, Unit::Count) << std::endl
        << BOLD("\tAlloc'd Memory    ") << printUnit(g_memstats.total_alloc_memory, Unit::Bytes) << "\n"
        << BOLD("\tSurvival Rate     ") << printUnit(((double)g_memstats.total_promotions / (double)g_memstats.total_alloc_count) * 100.0, Unit::Percentage) << "\n";

    std::cout << ss.str();
}

static void update_extrema(Stats& s, double time) noexcept 
{
    if(time > s.max) { 
        s.max = time;  
    }
    if(time < s.min) { 
        s.min = time;
    }
}

static void update_stats(Stats& stats, double time) noexcept
{
    // Welford's algorithm
    stats.count++;
    double delta = time - stats.mean;
    stats.mean += delta / stats.count;
    double delta2 = time - stats.mean;
    stats.M2 += delta * delta2;
    stats.total += time;

    update_extrema(stats, time);
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
    for(int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        total += buckets[i];
    }
    
    if(total == 0) {
        return 0.0;
    }
    
    size_t target_count = static_cast<size_t>(total * percentile);
    size_t cumulative = 0;
    
    for(int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        cumulative += buckets[i];
        if (cumulative >= target_count) {
            return i * BUCKET_VARIANCE;
        }
    }
    
    return (MAX_MEMSTATS_BUCKETS - 1) * BUCKET_VARIANCE;
}

void update_collection_stats(MemStats& ms, double time) noexcept 
{
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

// We dont need this, just use total from Stats
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
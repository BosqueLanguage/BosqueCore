#include "memstats.h"

#ifdef MEM_STATS

#include <cmath>
#include <iomanip>

MemStats g_memstats{};

static double calcStddev(const Stats& stats) noexcept;
static double calculate_percentile_from_buckets(const size_t* buckets, double percentile) noexcept; 

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
	switch(UNIT) { \
		case Unit::Count:        STREAM << V << CNT; break; \
		case Unit::Microseconds: STREAM << V << SEC; break; \
		case Unit::Bytes:        STREAM << V << BYTE; break; \
		default: break; \
	} \

void updateTotalTime()
{
    auto now = std::chrono::high_resolution_clock::now();
    std::chrono::duration<Time, std::micro> dur = now.time_since_epoch();
    g_memstats.total_time = 
		dur.count() - g_memstats.start_time - g_memstats.overhead_time;
}

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
    std::string mean = printUnit(s.mean, Unit::Microseconds);
    std::string std_dev = printUnit(calcStddev(s), Unit::Microseconds);
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

void MemStats::perfDump(Phase p)
{
    switch(p) {
        case Phase::Collection:
            formatPerf("Collection", this->collection_stats, 
				this->collection_times);
            break;
        case Phase::Nursery:
            formatPerf("Nursery", this->nursery_stats, this->nursery_times);
            break;
        case Phase::RC_Old:
            formatPerf("RC Old", this->rc_stats, this->rc_times);           
            break;
        default: break;
    }
}

void MemStats::statisticsDump()
{
    std::stringstream ss;
    ss  << BOLD("Statistics:\n")
        << BOLD("\tTotal Time        ") << printUnit(this->total_time, Unit::Microseconds) << std::endl 
        << BOLD("\tTime Collecting   ") << printUnit((this->collection_stats.total / g_memstats.total_time) * 100.0, Unit::Percentage) << std::endl
        << BOLD("\tTotal Collections ") << printUnit(this->collection_stats.count, Unit::Count) << std::endl
        << BOLD("\tTotal Pages       ") << printUnit(this->total_pages, Unit::Count) << std::endl
        << BOLD("\tMax Live Heap     ") << printUnit(this->max_live_heap, Unit::Bytes) << "\n"
        << BOLD("\tHeap Size         ") << printUnit(this->total_pages * BSQ_BLOCK_ALLOCATION_SIZE, Unit::Bytes) << "\n"
        << BOLD("\tAlloc Count       ") << printUnit(this->total_alloc_count, Unit::Count) << std::endl
        << BOLD("\tAlloc'd Memory    ") << printUnit(this->total_alloc_memory, Unit::Bytes) << "\n"
        << BOLD("\tSurvival Rate     ") << printUnit(((double)this->total_promotions / (double)this->total_alloc_count) * 100.0, Unit::Percentage) << "\n";

    std::cout << ss.str();
}

static void updateBucket(size_t* bucket, double time) noexcept 
{
    int index = static_cast<int>((time * (1.0 / BUCKET_VARIANCE)) + 0.5);
    if(index >= MAX_MEMSTATS_BUCKETS) { 
        bucket[MAX_MEMSTATS_BUCKETS - 1]++;
    }
    else {
        bucket[index]++;
    }
}

void Stats::update(double time) noexcept
{
    // Welford's algorithm
    this->count++;
    double delta = time - this->mean;
    this->mean += delta / this->count;
    double delta2 = time - this->mean;
    this->M2 += delta * delta2;
    this->total += time;

    if(time > this->max) { 
    	this->max = time;  
    }
    if(time < this->min) { 
        this->min = time;
    }
}

void MemStats::updateStats(Stats& trgt, Time* list, double t) noexcept
{
	list[trgt.count % TIMES_LIST_SIZE] = t;
	trgt.update(t);
}

void MemStats::updateTelemetry(Phase p, double t) noexcept
{
	using enum Phase;
	switch(p) {
		case Collection: 
			this->updateStats(this->collection, this->collection_times, t); 
			updateBucket(this->collection_buckets, t);
			break;
		case Nursery: 
			this->updateStats(this->nursery, this->nursery_times, t); 
			updateBucket(this->nursery_buckets, t);
			break;
		case RC_Old: 
			this->updateStats(this->rc, this->rc_times, t); 
			updateBucket(this->rc_buckets, t);		
			break;
		default: assert(false && "Invalid phase in updateTelemetry!\n");
	}
}

// I guess someone could use this in the middle of running an application 
// and not kill the thread which could mess up calculations since we might
// merge old times twice
// -- i guess we should just use explicit indexes?
static inline void processTimesList(Stats& dst, Time* src) noexcept
{
	for(unsigned i = 0; i < TIMES_LIST_SIZE; i++) {
		dst.update(src[i]);
	}
}

// To prevent incorrect mean calculations when merging into our global memstats
// we maintain lists of stats for each collection phase and periodically work
// through each stat entry, updating g_memstats 
void MemStats::tryUpdateGlobalStats() noexcept
{
	std::lock_guard lk(g_gctelemetrylock);
	if(this->collection.count == TIMES_LIST_SIZE) {
		processTimesList(g_memstats.collection, this->collection_times);	
		processTimesList(g_memstats.nursery, this->nursery_times);
		processTimesList(g_memstats.rc, this->rc_times);
	}
}

static double calcStddev(const Stats& stats) noexcept 
{
    if(stats.count < 2) {
        return 0.0;
    }

    return std::sqrt(stats.M2 / stats.count);
}

static double calculate_percentile_from_buckets(const size_t* buckets, double percentile) noexcept 
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

static std::string generate_bucket_data(size_t buckets[MAX_MEMSTATS_BUCKETS]) noexcept 
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
std::string generateFormattedMemstats(MemStats& ms) noexcept
{
    std::string header = "{" + std::to_string(BUCKET_VARIANCE) 
        + ", " + std::to_string(MAX_MEMSTATS_BUCKETS) + "}\n
    std::string collection_data = generate_bucket_data(ms.collection_times);
    std::string collection_times = "<Collection Times>" + collection_data;

    std::string nursery_data = generate_bucket_data(ms.nursery_times);
    std::string nursery_times = "<Nursery Times>" + nursery_data;

    std::string rc_data = generate_bucket_data(ms.rc_times);
    std::string rc_times = "<RC Times>" + rc_data;

    return header + collection_times + nursery_times + rc_times;
}

static void mergeBuckets(size_t* dst, size_t* src) noexcept
{
	for(unsigned i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
		dst[i] = src[i];	
	}
}

void MemStats::merge(MemStats& trgt)
{
	this->total_alloc_count +=  trgt.total_alloc_count;
	this->total_alloc_memory += trgt.total_alloc_memory;
	this->total_live_bytes +=   trgt.total_live_bytes;
	this->total_live_objects += trgt.total_live_objects;
	this->total_promotions +=   trgt.total_promotions;
	this->total_pages +=      	trgt.total_pages;

	processTimesList(g_memstats.collection, this->collection_times);	
	processTimesList(g_memstats.nursery, this->nursery_times);
	processTimesList(g_memstats.rc, this->rc_times);

	this->overhead_time += trgt.overhead_time;
	this->total_time += trgt.total_time;

	if(trgt.max_live_heap > this->max_live_heap) {
		this->max_live_heap = trgt.max_live_heap;
	}

	mergeBuckets(this->collection_times, trgt.collection_times);
	mergeBuckets(this->nursery_times, trgt.nursery_times);
	mergeBuckets(this->rc_times, trgt.rc_times);

	// Should clear ms (incase we want to merge without killing ms's thread)
	trgt = {0};
}

#endif // MEM_STATS

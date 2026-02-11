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

void MemStats::updateTotalTime()
{
    auto now = std::chrono::high_resolution_clock::now();
    std::chrono::duration<Time, std::micro> dur = now.time_since_epoch();
    this->total_time = 
		dur.count() - this->start_time - this->overhead_time;
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

void MemStats::printPerfHeader()
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
				this->collection_buckets);
            break;
        case Phase::Nursery:
            formatPerf("Nursery", this->nursery_stats, this->nursery_buckets);
            break;
        case Phase::RC_Old:
            formatPerf("RC Old", this->rc_stats, this->rc_buckets);           
            break;
        default: break;
    }
}

void MemStats::statisticsDump()
{
    std::stringstream ss;
    ss  << BOLD("Statistics:\n")
        << BOLD("\tTotal Time        ") << printUnit(this->total_time, Unit::Microseconds) << std::endl 
        << BOLD("\tTime Collecting   ") << printUnit((this->collection_stats.total / this->total_time) * 100.0, Unit::Percentage) << std::endl
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

static inline void updateStats(Stats& trgt, Time* list, double t) noexcept
{
	list[trgt.count % TIMES_LIST_SIZE] = t;
	trgt.update(t);
}

void MemStats::updateTelemetry(Phase p, double t) noexcept
{
	using enum Phase;
	switch(p) {
		case Collection: 
			updateStats(this->collection_stats, this->collection_times, t); 
			updateBucket(this->collection_buckets, t);
			break;
		case Nursery: 
			updateStats(this->nursery_stats, this->nursery_times, t); 
			updateBucket(this->nursery_buckets, t);
			break;
		case RC_Old: 
			updateStats(this->rc_stats, this->rc_times, t); 
			updateBucket(this->rc_buckets, t);		
			break;
		default: assert(false && "Invalid phase in updateTelemetry!\n");
	}
}

// I think this notion of 'dst' is confusing as it would make more sense
// to merge into 'this'

static inline void processTimesList(Stats& dst, Time* src) noexcept
{
	for(unsigned i = 0; i < ; i++) {
		dst.update(src[i]);
	}
}

void MemStats::processAllTimesLists(Stats& src) noexcept
{
	processTimesList(this->collection_stats, dst.collection_times);	
	processTimesList(this->nursery_stats, dst.nursery_times);
	processTimesList(this->rc_stats, dst.rc_times);
}

void MemStats::tryMergeTimesLists(MemStats& src, bool is_global_memstats, 
	bool force) noexcept
{
	if(this->collection_stats.count == TIMES_LIST_SIZE || force) {
		if(is_global_memstats) {
			std::lock_guard lk(g_gctelemetrylock);
			processAllTimesLists(src);
		}
		else {
			processAllTimesLists(src);	
		}
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
        + ", " + std::to_string(MAX_MEMSTATS_BUCKETS) + "}\n";
    std::string collection_data = generate_bucket_data(ms.collection_buckets);
    std::string collection_times = "<Collection Times>" + collection_data;

    std::string nursery_data = generate_bucket_data(ms.nursery_buckets);
    std::string nursery_times = "<Nursery Times>" + nursery_data;

    std::string rc_data = generate_bucket_data(ms.rc_buckets);
    std::string rc_times = "<RC Times>" + rc_data;

    return header + collection_times + nursery_times + rc_times;
}

static void mergeBuckets(size_t* dst, size_t* src) noexcept
{
	for(unsigned i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
		dst[i] = src[i];	
	}
}

void MemStats::mergeNonTimeLists(MemStats& src)
{
	this->total_alloc_count +=  src.total_alloc_count;
	this->total_alloc_memory += src.total_alloc_memory;
	this->total_live_bytes +=   src.total_live_bytes;
	this->total_live_objects += src.total_live_objects;
	this->total_promotions +=   src.total_promotions;
	this->total_pages +=      	src.total_pages;

	processTimesList(this->collection_stats, src.collection_times);	
	processTimesList(this->nursery_stats, src.nursery_times);
	processTimesList(this->rc_stats, src.rc_times);

	this->overhead_time += src.overhead_time;
	this->total_time += src.total_time;

	if(src.max_live_heap > this->max_live_heap) {
		this->max_live_heap = src.max_live_heap;
	}

	mergeBuckets(this->collection_buckets, src.collection_buckets);
	mergeBuckets(this->nursery_buckets, src.nursery_buckets);
	mergeBuckets(this->rc_buckets, src.rc_buckets);
}

void MemStats::merge(MemStats& src, bool is_global_memstats, bool force)
{
	if(is_global_memstats) {
		std::lock_guard lk(g_gctelemetrylock);
		this->mergeNonTimeLists(src);
	}
	else {
		this->mergeNonTimeLists(src);
	}
	this->tryMergeTimesLists(src, is_global_memstats, force);	

	// TODO Should clear ms (incase we want to merge without killing ms's thread)
	//src = {0};
}

#endif // MEM_STATS

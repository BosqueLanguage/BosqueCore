#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ
{
    using Time = size_t;

    class SingleCollectStat
    {
    public:
        Time timetotal_us;
        Time young_time_us;
        Time rc_time_us;
    };

    class UtilizationStat
    {
    public:
        size_t count_0_30;
        size_t count_30_70;
        size_t count_70_100;
    };

    class HeapStats
    {
    public: 
        size_t totalpages;
        size_t livebytes;
        size_t freebytes;

        UtilizationStat overallutilizations;

        size_t hotnurserycount;
        UtilizationStat nurseryutilizations;

        size_t pagesetcount;
        UtilizationStat pagesetutilizations;
    };

    class CollectionDataInfo
    {
    public:
        size_t nurserypages;

        size_t totalprocessed;
        size_t inplace;
        size_t evacuated;

        size_t indirectrcreclaims;
        size_t quickreclaims;
        size_t pendreclaims;

        size_t startingrcpends;
        size_t finalrcpends;
    };

    class MemStats {
    public:
        constexpr static size_t RRSTATS_SIZE = 50;

        inline static size_t computeIntervalInMicroseconds(struct timespec start, struct timespec end) 
        {
            return ((end.tv_nsec - start.tv_nsec)) / 1000 + (end.tv_sec - start.tv_sec) * 1000000;
        }

        inline static std::tuple<Time, Time, Time> computeMinMaxAvgPauses(const std::array<SingleCollectStat, RRSTATS_SIZE>& stats) 
        {
            Time min_total = std::numeric_limits<Time>::max();
            Time max_total = 0;
            Time avg_total = 0;

            size_t count = 0;
            for(size_t i = 0; i < RRSTATS_SIZE; i++) {
                auto stat = stats[i];
                if(stat.timetotal_us == 0) {
                    continue; //skip uninitialized slots
                }

                count++;
                if(stat.timetotal_us < min_total) {
                    min_total = stat.timetotal_us;
                }
                if(stat.timetotal_us > max_total) {
                    max_total = stat.timetotal_us;
                }
                avg_total += stat.timetotal_us;
            }
            
            Time avg_val = avg_total / std::max(count, (size_t)1);
            return std::make_tuple(min_total != std::numeric_limits<Time>::max() ? min_total : 0, max_total, avg_val);
        }

        SingleCollectStat totalstats = {0, 0, 0};

        size_t rstatsidx = 0;
        std::array<SingleCollectStat, RRSTATS_SIZE> rrstats{};

        CollectionDataInfo collectstats{};
        HeapStats heapstats{};

        size_t totalpages = 0;

        size_t collectioncount = 0;
        size_t totalallocs = 0;
        size_t totalbytes = 0;

        void processallocpage()
        {
            this->totalpages += 1;
        }

        void processalloc(size_t bytes) 
        {
            this->totalallocs += 1;
            this->totalbytes += bytes;
        }

        void processcollect(struct timespec tstart, struct timespec twalkdone, struct timespec trcdone, struct timespec tend) 
        {
            this->collectioncount += 1;

            auto total = computeIntervalInMicroseconds(tstart, tend);
            auto walk = computeIntervalInMicroseconds(tstart, twalkdone);
            auto rc = computeIntervalInMicroseconds(twalkdone, trcdone);

            this->totalstats = {this->totalstats.timetotal_us + total, this->totalstats.young_time_us + walk, this->totalstats.rc_time_us + rc};
            rrstats[rstatsidx] = {total, walk, rc};
            rstatsidx = (rstatsidx + 1) % RRSTATS_SIZE;
        }

        MemStats() { ; }

        void dump(std::ostream& out)
        {
            auto [min_time, max_time, avg_time] = computeMinMaxAvgPauses(rrstats);

            out << "MEMSTATS: Total Time: " << this->totalstats.timetotal_us / 1000 << "ms, Young Time: " << this->totalstats.young_time_us / 1000 << "ms, RC Time: " << this->totalstats.rc_time_us / 1000 << "ms" << std::endl;
            out << "Collection (Approx) Distribution -- Min: " << min_time << "us, Max: " << max_time << "us, Avg: " << avg_time << "us" << std::endl;
            out << "Total Pages: " << this->totalpages << ", Total Collections: " << this->collectioncount << ", Total Allocations: " << this->totalallocs << ", Total Bytes: " << this->totalbytes << std::endl;

#if GC_METRICS_DETAILED
            const CollectionDataInfo& stats = this->collectstats;
            out << std::endl << "Collection Stats (Most Recent): " << std::endl;
            out << "Nursery Pages: " << stats.nurserypages << std::endl;
            out << "Total Objects Processed: " << stats.totalprocessed << ", In Place Promoted: " << stats.inplace << ", Evacuated: " << stats.evacuated << std::endl;
            out << "Indirect RC Reclaims: " << stats.indirectrcreclaims << ", Quick Reclaims: " << stats.quickreclaims << ", Pending Reclaims: " << stats.pendreclaims << std::endl;
            out << "Starting RC Pending: " << stats.startingrcpends << ", Final RC Pending: " << stats.finalrcpends << std::endl;
#endif

#if GC_VALIDATE
            const HeapStats& hstats = this->heapstats;
            out << std::endl << "Heap Stats (Most Recent): " << std::endl;
            out << "Total Pages: " << hstats.totalpages << ", Live Bytes: " << hstats.livebytes << ", Free Bytes: " << hstats.freebytes << std::endl;
            out << "Overall Utilization: 0-30%: " << hstats.overallutilizations.count_0_30 << ", 30-70%: " << hstats.overallutilizations.count_30_70 << ", 70-100%: " << hstats.overallutilizations.count_70_100 << std::endl;
            out << "Hot Nursery Pages: " << hstats.hotnurserycount << ", Nursery Utilization: 0-30%: " << hstats.nurseryutilizations.count_0_30 << ", 30-70%: " << hstats.nurseryutilizations.count_30_70 << ", 70-100%: " << hstats.nurseryutilizations.count_70_100 << std::endl;
            out << "Pageset Count: " << hstats.pagesetcount << ", Pageset Utilization: 0-30%: " << hstats.pagesetutilizations.count_0_30 << ", 30-70%: " << hstats.pagesetutilizations.count_30_70 << ", 70-100%: " << hstats.pagesetutilizations.count_70_100 << std::endl; 
#endif
        }
    };

    extern MemStats g_memstats;
}

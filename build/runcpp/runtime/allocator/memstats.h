#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ
{
    using Time = size_t;

    class SingleCollectStat
    {
    public:
        Time timetotal_ms = 0;
        Time young_time_ms = 0;
        Time rc_time_ms = 0;
    };

    class MemStats {
    public:
        constexpr static size_t RRSTATS_SIZE = 10;

        constexpr static size_t computeIntervalInMic(struct timespec start, struct timespec end) 
        {
            return (end.tv_nsec - start.tv_nsec) / 1000;
        }

        constexpr static std::tuple<Time, Time, Time> computeMinMaxAvgPauses(const std::array<SingleCollectStat, RRSTATS_SIZE>& stats) 
        {
            Time min_total = std::numeric_limits<Time>::max();
            Time max_total = 0;
            Time avg_total = 0;

            size_t count = 0;
            for(size_t i = 0; i < RRSTATS_SIZE; i++) {
                auto stat = stats[i];
                if(stat.timetotal_ms == 0) {
                    continue; //skip uninitialized slots
                }

                count++;
                if(stat.timetotal_ms < min_total) {
                    min_total = stat.timetotal_ms;
                }
                if(stat.timetotal_ms > max_total) {
                    max_total = stat.timetotal_ms;
                }
                avg_total += stat.timetotal_ms;
            }
            
            Time avg_total = avg_total / std::max(count, (size_t)1);
            return std::make_tuple(min_total != std::numeric_limits<Time>::max() ? min_total : 0, max_total, avg_total);
        }

#if GC_METRICS_BASIC
        SingleCollectStat totalstats = {0, 0, 0};

        size_t rstatsidx = 0;
        std::array<SingleCollectStat, RRSTATS_SIZE> rrstats{};

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

            auto total = computeIntervalInMic(tstart, tend);
            auto walk = computeIntervalInMic(tstart, twalkdone);
            auto rc = computeIntervalInMic(twalkdone, trcdone);

            this->totalstats = {this->totalstats.timetotal_ms + total, this->totalstats.young_time_ms + walk, this->totalstats.rc_time_ms + rc};
            rrstats[rstatsidx] = {total, walk, rc};
            rstatsidx = (rstatsidx + 1) % RRSTATS_SIZE;
        }
#endif

        constexpr static std::chrono::microseconds time_in_micros(std::chrono::nanoseconds delta) 
        {
            return std::chrono::duration_cast<std::chrono::microseconds>(delta);
        }

        constexpr static std::chrono::milliseconds time_in_millis(std::chrono::nanoseconds delta) 
        {
            return std::chrono::duration_cast<std::chrono::milliseconds>(delta);
        }

        MemStats() { ; }

        void dump(std::ostream& out)
        {
#if GC_METRICS_BASIC
            auto [min_time, max_time, avg_time] = computeMinMaxAvgPauses(rrstats);

            out << "MEMSTATS: Total Time: " << this->totalstats.timetotal_ms << ", Young Time: " << this->totalstats.young_time_ms << ", RC Time: " << this->totalstats.rc_time_ms << std::endl;
            out << "Collection (Approx) Distribution -- Min: " << min_time << ", Max: " << max_time << ", Avg: " << avg_time << std::endl;
            out << "Total Pages: " << this->totalpages << ", Total Collections: " << this->collectioncount << ", Total Allocations: " << this->totalallocs << ", Total Bytes: " << this->totalbytes << std::endl;
#endif
        }
    };

    extern MemStats g_memstats;
}

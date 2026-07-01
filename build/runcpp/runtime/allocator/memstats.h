#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ
{
    using Time = size_t;

    class SingleCollectStat
    {
    public:
        Time timetotal_us = 0;
        Time young_time_us = 0;
        Time rc_time_us = 0;
    };

    class MemStats {
    public:
        constexpr static size_t RRSTATS_SIZE = 10;

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
        }
    };

    extern MemStats g_memstats;
}

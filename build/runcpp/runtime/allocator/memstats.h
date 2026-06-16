#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ
{
    using Time = std::chrono::milliseconds;

    class MemStats {
    public:
#if GC_METRICS_BASIC
        Time timetotal = std::chrono::milliseconds(0);
        Time timeyoung = std::chrono::milliseconds(0);
        Time timerc = std::chrono::milliseconds(0);

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

        void processcollect(Time total, Time young, Time rc) 
        {
            this->collectioncount += 1;

            this->timetotal += total;
            this->timeyoung += young;
            this->timerc += rc;
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

        void reset() 
        {
            *this = MemStats();
        }
    };

    extern MemStats g_memstats;
}

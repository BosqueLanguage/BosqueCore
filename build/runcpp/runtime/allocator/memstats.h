#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ
{
    using Time = std::chrono::milliseconds;

    class MemStats {
    public:
        Time timetotal = std::chrono::milliseconds(0);
        Time timeyoung = std::chrono::milliseconds(0);
        Time timerc = std::chrono::milliseconds(0);

#if GC_DIAG_LEVEL_1
        size_t collectioncount = 0;
        size_t totalallocs = 0;
        size_t totalbytes = 0;

        void processcollect(Time total, Time young, Time rc) 
        {
            this->collectioncount += 1;

            this->timetotal += total;
            this->timeyoung += young;
            this->timerc += rc;
        }

        void processalloc(size_t bytes) 
        {
            this->totalallocs += 1;
            this->totalbytes += bytes;
        }
#else
        constexpr void processcollect(Time total, Time young, Time rc);
        constexpr void processalloc(size_t bytes) { ; }
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
    };

    extern MemStats g_memstats;
}

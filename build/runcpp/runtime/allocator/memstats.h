#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ
{
    using Time = double;

    class MemStats {
    public:
#if GC_DIAG_LEVEL_1
        size_t totalallocs = 0;
        size_t totalbytes = 0;

        void processalloc(size_t bytes) {
            this->totalallocs += 1;
            this->totalbytes += bytes;
        }
#else
        constexpr void processalloc(size_t bytes) { ; }
#endif

        Time timetotal = 0.0;
        Time timeyoung = 0.0;
        Time timerc = 0.0;

        MemStats() { ; }
    };
}

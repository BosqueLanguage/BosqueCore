#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ
{
    using Time = std::chrono::milliseconds;

    class MemStats {
    public:
#if GC_DIAG_LEVEL_1
        Time timetotal = std::chrono::milliseconds(0);
        Time timeyoung = std::chrono::milliseconds(0);
        Time timerc = std::chrono::milliseconds(0);

        size_t collectioncount = 0;
        size_t totalallocs = 0;
        size_t totalbytes = 0;

        void processalloc(size_t bytes) 
        {
            this->totalallocs += 1;
            this->totalbytes += bytes;
        }

        void processallocof(uint16_t idx, void* ptr) 
        {
            ;
        }

        void processcollect(Time total, Time young, Time rc) 
        {
            this->collectioncount += 1;

            this->timetotal += total;
            this->timeyoung += young;
            this->timerc += rc;
        }
#if GC_DIAG_LEVEL_2
        size_t total_root_promotions = 0;
        size_t total_evac_promotions = 0;

        size_t total_rc_root_incs = 0;
        size_t total_rc_root_decs = 0;
        size_t total_rc_std_incs = 0;
        size_t total_rc_std_decs = 0;

        size_t total_pending_enqueue = 0;
        size_t total_rc_reclaims = 0;

        void processpromotion(void* ptr, bool isroot) 
        {
            if(isroot) {
                this->total_root_promotions += 1;
            }
            else {
                this->total_evac_promotions += 1;
            }
        }

        void processrootinc(void* ptr) 
        { 
            this->total_rc_root_incs += 1; 
        }
        
        void processrootdec(void* ptr) 
        { 
            this->total_rc_root_decs += 1; 
        }
        
        void processstdinc(void* ptr) 
        { 
            this->total_rc_std_incs += 1; 
        }
        
        void processstddec(void* ptr) 
        { 
            this->total_rc_std_decs += 1; 
        }

        void processpushpendingdelete(void* ptr) 
        { 
            this->total_pending_enqueue += 1; 
        }

        void processreclaimrc(void* ptr) 
        { 
            this->total_rc_reclaims += 1; 
        }
#endif
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

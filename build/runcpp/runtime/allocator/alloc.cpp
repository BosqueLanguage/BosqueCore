#include "alloc.h"

namespace ᐸRuntimeᐳ
{
    thread_local AllocatorThreadLocalInfo tl_alloc_info;
    AllocatorGlobalInfo g_alloc_info;

    void AllocatorThreadLocalInfo::initialize(void** caller_rbp, void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs)
    {
        this->collectfp = _collectfp;
        this->gcallocs = gcallocs;
    }
	
    void AllocatorThreadLocalInfo::cleanup()
    {
        for(auto iter = this->gcallocs.begin(); iter != this->gcallocs.end(); iter++) {
            iter->second->cleanup();
        }
    
        this->gcallocs.clear();
    }

    void collect()
    {
        ;
    }

    bool AllocatorGlobalInfo::loadGlobalRootsToProc(std::vector<void*>& possibleroots)
    {
        this->g_globals_mutex.lock();
        if(this->g_globals_lastproc == this->g_globals_end) {
            this->g_globals_mutex.unlock();
            return false;
        }

        std::copy(this->g_globals_lastproc, this->g_globals_end, std::back_inserter(possibleroots));
        return true;
    }

    void AllocatorGlobalInfo::unloadGlobalRootsFromProc(bool processed)
    {
        if(processed) {
            this->g_globals_lastproc = this->g_globals_end;
            this->g_globals_mutex.unlock();
        }
    }

    bool AllocatorGlobalInfo::isAllocatedAddress(void* addr, GCMetadata& m)
    {
        //Check address could be in middle of allocated object too!!
        assert(false);

        /*
        bool pointsToObjectStart(void* addr) noexcept 
    {
        uintptr_t offset = reinterpret_cast<uintptr_t>(addr) & GC_PAGE_MASK; 
        PageInfo* p = PageInfo::extractPageFromPointer(addr);
	    if(offset < (sizeof(PageInfo) + METADATA_SEG_SIZE(p))) {
            return false;
        }

        uintptr_t start = GET_SLOT_START_FROM_OFFSET(offset, p);
        return start % p->realsize == 0;
    }

    bool processPotentialPtr(void* addr, std::vector<void*>& roots)
    { 
	    if(!GlobalPageGCManager::g_gc_page_manager.pagetableQuery(addr) || !pointsToObjectStart(addr))
	    {
            return false;
        }
        */
    }
}

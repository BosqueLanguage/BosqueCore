#include "alloc.h"

namespace ᐸRuntimeᐳ
{
#if BSQ_ALLOCATOR_USE_MALLOC
    std::map<void*, GCAllocatorImpl*> GCAllocatorImpl::x_all_alloc_to_allocator_map{};
#endif

    thread_local AllocatorThreadLocalInfo tl_alloc_info;
    AllocatorGlobalInfo g_alloc_info;

    void AllocatorThreadLocalInfo::initialize(std::thread::id threadid, void** caller_rbp, void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs)
    {
        this->native_stack_base = caller_rbp;
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

    bool AllocatorGlobalInfo::isAllocatedAddress(void* addr, GCMetadata*& meta, void*& raddr)
    {
#if BSQ_ALLOCATOR_USE_MALLOC
        if(GCAllocatorImpl::x_all_alloc_to_allocator_map.empty()) {
            return false;
        }

        auto aii = GCAllocatorImpl::x_all_alloc_to_allocator_map.lower_bound(addr);
        aii--;

        if(!aii->second->isAddrInValidObject(addr, meta, raddr)) {
            return false;
        }

        return aii->second->isAddrSuitableCategory(meta);
    }
#else
    //TODO -- page version is more complex and must check
        // - Is the page allocated at all (in the table map)
        // - If so is the location in (many be in middle) of valid object in the page
        //   - Is the object allocated
        //   - If so then is the object young (and of the same threadid) OR is it an RC object
#endif
}

#include "alloc.h"

namespace ᐸRuntimeᐳ
{
#if BSQ_ALLOCATOR_USE_MALLOC
    std::map<void*, GCAllocatorImpl*> GCAllocatorImpl::x_all_alloc_to_allocator_map{};
#endif

    thread_local AllocatorThreadLocalInfo tl_alloc_info;
    AllocatorGlobalInfo g_alloc_info;

    void runCollect()
    {
        tl_alloc_info.collectfp();
    }

    PageInfo* PageInfo::setPageMetaData(void* vpp, GCAllocatorImpl* gcalloc, std::thread::id threadid, size_t agectr, PageInfo* prev, PageInfo* next)
    {
        PageInfo* pp = (PageInfo*)vpp;

        uint32_t p2sizeshift = std::bit_ceil(gcalloc->alloctype->slotcount);
        uint32_t p2size = std::pow(2, p2sizeshift);

        uint32_t objcount = (GC_PAGE_SIZE - sizeof(PageInfo)) / ((p2size + 1) * 8);

        pp->typeinfo = gcalloc->alloctype;
        pp->gcalloc = gcalloc;
        pp->threadid = threadid;

        pp->freelistidx = META_FREE_LIST_OOM_SENTINAL;
        pp->freecount = -1;
        pp->esize = objcount;

        pp->mdata = (AtomicGCMetadata*)((uint8_t*)pp + sizeof(PageInfo));
        pp->data = (void**)((void**)pp->mdata + objcount);
        pp->size2shift = p2sizeshift;

        pp->age = agectr;
        pp->prev = prev;
        pp->next = next;

        return pp;
    }

    void* PageInfo::reset(PageInfo* pp)
    {
        pp->typeinfo = nullptr;
        pp->gcalloc = nullptr;
        pp->threadid = std::thread::id{};

        pp->freelistidx = META_FREE_LIST_OOM_SENTINAL;
        pp->freecount = -1;

        pp->data = nullptr;
        pp->mdata = nullptr;
        pp->size2shift = 0;

        pp->age = 0;
        pp->prev = nullptr;
        pp->next = nullptr;

        return (void*)pp;
    }

    void PageInfo::rebuild(size_t agectr)
    {
        this->freelistidx = META_FREE_LIST_OOM_SENTINAL;
        this->freecount = 0;
        this->age = agectr;
 
        for(int64_t i = this->esize - 1; i > 0; i--) {
            AtomicGCMetadata* meta = this->getMetadataFromIndexInPage(i);

            if(!gcIsAllocated(meta) | gcIsYoung(meta)) {
                gcProcessSweep(meta);
                   
                gcSetFreeListBits(meta, this->freelistidx);
                this->freelistidx = i;
                this->freecount++;
            }
        }
    }

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

    void AllocatorGlobalInfo::initializeGlobalRegion(void* data)
    {
        this->g_globals = data;
        this->g_globals_lastproc = (void**)this->g_globals;
        this->g_globals_end = (void**)this->g_globals;
    }
    
    void* AllocatorGlobalInfo::getGlobalRegionStorageOfSize(size_t k)
    {
        void* slot = (void*)this->g_globals_end;
        this->g_globals_end = (void**)((uint8_t*)this->g_globals_end + k);

        return slot;
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

    bool AllocatorGlobalInfo::isAllocatedAddress(void* addr, const AtomicGCMetadata* meta, void*& raddr)
    {
#if BSQ_ALLOCATOR_USE_MALLOC
        if(GCAllocatorImpl::x_all_alloc_to_allocator_map.empty()) {
            return false;
        }

        auto aii = GCAllocatorImpl::x_all_alloc_to_allocator_map.lower_bound(addr);
        if(aii != GCAllocatorImpl::x_all_alloc_to_allocator_map.begin() && aii->first != addr) {
            aii--;
        }

        if(!aii->second->isAddrInValidObject(addr, meta, raddr)) {
            return false;
        }

        return aii->second->isAddrSuitableCategory(meta, raddr);
    }
#else
    //TODO -- page version is more complex and must check
        // - Is the page allocated at all (in the table map)
        // - If so is the location in (many be in middle) of valid object in the page
        //   - Is the object allocated
        //   - If so then is the object young (and of the same threadid) OR is it an RC object
#endif
}

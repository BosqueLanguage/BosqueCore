#include "./gc_validation.h"

namespace ᐸRuntimeᐳ
{
    std::pair<size_t, size_t> processInfoForSinglePage(const PageInfo* pp, UtilizationStat& stat, const std::unordered_set<void*>& pendingdeletes)
    {
        std::unordered_set<void*> freelistset;
        void* freecur = pp->freelist;
        while(freecur != nullptr) {
            void* next = *((void**)freecur);
            
            //This is a free list entry that is also in the pending delete list -- this is an error
            assert(!pendingdeletes.contains(freecur));
            
            //This is a free list entry that is already in the free list set -- this is an error
            assert(!freelistset.contains(freecur));
            
            //This is a free list entry that has some other types of bits set -- this is an error
            AtomicGCMetadata* freemeta = pp->getMetadataForObj(freecur);
            assert((freemeta->load(std::memory_order::relaxed) & META_BIT_RC_BITS_MASK) == 0);

            freelistset.insert(freecur);
            freecur = next;
        }

        //now walk the page to check that the free list and the pending deletes are consistent with the metadata
        size_t livebytes = 0;
        size_t freebytes = 0;
        size_t entrybytes = pp->typeinfo->bytesize;
        for(int64_t i = pp->esize - 1; i >= 0; i--) {
            AtomicGCMetadata* meta = pp->getMetadataFromIndexInPage(i);

            if(!gcIsAllocated(meta)) {
                freebytes += entrybytes;
                void* obj = pp->getObjectFromIndexInPage(i);
                assert(freelistset.contains(obj));
            }
            else {
                livebytes += entrybytes;
                void* obj = pp->getObjectFromIndexInPage(i);
                assert(!freelistset.contains(obj));

                if((meta->load(std::memory_order::relaxed) & META_BIT_IS_DELETE_PENDING) != 0) {
                    //If this is a delete pending object, it should be in the pending deletes set
                    assert(pendingdeletes.contains(obj));
                }
                else {
                    //If this is a live RC object, it should have either the unique or shared RC bit set
                    assert((meta->load(std::memory_order::relaxed) & (META_BIT_IS_RC_UNIQUE | META_BIT_IS_RC_SHARED)) != 0);

                    //If this is a live RC object, it should have a non-zero RC count (or unique address set)
                    assert((meta->load(std::memory_order::relaxed) & META_BIT_RC_MASK) != 0);

                    //If this is a live RC object, it should not be in the pending deletes set
                    assert(!pendingdeletes.contains(obj));
                }
            }
        }

        double utilization = ((double)pp->freecount / (double)pp->esize) * 100.0;
        if(utilization < 30.0) {
            stat.count_0_30++;
        }
        else if(utilization < 70.0) {
            stat.count_30_70++;
        }
        else {
            stat.count_70_100++;
        }

        return std::make_pair(livebytes, freebytes);
    }

    std::pair<size_t, size_t> processInfoForSingleEvacPage(const PageInfo* pp, const std::unordered_set<void*>& pendingdeletes)
    {
        std::unordered_set<void*> freelistset;
        void* freecur = pp->freelist;
        while(freecur != nullptr) {
            void* next = *((void**)freecur);
            
            //This is a free list entry that is also in the pending delete list -- this is an error
            assert(!pendingdeletes.contains(freecur));
            
            //This is a free list entry that is already in the free list set -- this is an error
            assert(!freelistset.contains(freecur));
            
            //This is a free list entry that has some other types of bits set -- this is an error
            AtomicGCMetadata* freemeta = pp->getMetadataForObj(freecur);
            assert((freemeta->load(std::memory_order::relaxed) & META_BIT_RC_BITS_MASK) == 0);

            freelistset.insert(freecur);
            freecur = next;
        }

        //now walk the page to check that the free list and the pending deletes are consistent with the metadata
        size_t livebytes = 0;
        size_t freebytes = 0;
        size_t entrybytes = pp->typeinfo->bytesize;
        for(int64_t i = pp->esize - 1; i >= 0; i--) {
            AtomicGCMetadata* meta = pp->getMetadataFromIndexInPage(i);

            if(!gcIsAllocated(meta)) {
                freebytes += entrybytes;
                //It might not be in the free list if it was RC collected (since we don't rebuild these pages)
            }
            else {
                livebytes += entrybytes;
                void* obj = pp->getObjectFromIndexInPage(i);
                assert(!freelistset.contains(obj));

                if((meta->load(std::memory_order::relaxed) & META_BIT_IS_DELETE_PENDING) != 0) {
                    //If this is a delete pending object, it should be in the pending deletes set
                    assert(pendingdeletes.contains(obj));
                }
                else {
                    //If this is a live RC object, it should have either the unique or shared RC bit set
                    assert((meta->load(std::memory_order::relaxed) & (META_BIT_IS_RC_UNIQUE | META_BIT_IS_RC_SHARED)) != 0);

                    //If this is a live RC object, it should have a non-zero RC count (or unique address set)
                    assert((meta->load(std::memory_order::relaxed) & META_BIT_RC_MASK) != 0);

                    //If this is a live RC object, it should not be in the pending deletes set
                    assert(!pendingdeletes.contains(obj));
                }
            }
        }

        //We are not going to track utilization for the active evacuation page since it is a special case

        return std::make_pair(livebytes, freebytes);
    }

    void processInfoForHotNurseryPages(const GCAllocatorImpl* allocator, HeapStats& stat, const std::unordered_set<void*>& pendingdeletes)
    {
        //This should be clear since we just processed the filled pages and moved them to the hot nursery pages
        assert(allocator->allocpage == nullptr);
        assert(allocator->nextalloc.second == META_FREE_LIST_OOM_SENTINAL);
        assert(allocator->filled_pages.empty());

        stat.totalpages += allocator->hot_nursery_pages.size();

        stat.hotnurserycount = allocator->hot_nursery_pages.size();
        for(auto iter = allocator->hot_nursery_pages.begin(); iter != allocator->hot_nursery_pages.end(); iter++) {
            auto [livebytes, freebytes] = processInfoForSinglePage(*iter, stat.nurseryutilizations, pendingdeletes);
            stat.livebytes += livebytes;
            stat.freebytes += freebytes;
        }

        stat.overallutilizations.count_0_30 += stat.nurseryutilizations.count_0_30;
        stat.overallutilizations.count_30_70 += stat.nurseryutilizations.count_30_70;
        stat.overallutilizations.count_70_100 += stat.nurseryutilizations.count_70_100;
    }

    void processInfoForActiveEvacPage(const GCAllocatorImpl* allocator, HeapStats& stat, const std::unordered_set<void*>& pendingdeletes)
    {
        if(allocator->evacpage == nullptr) {
            assert(allocator->nextevac.second == META_FREE_LIST_OOM_SENTINAL);

            return;
        }
            
        stat.totalpages++;
    
        auto [livebytes, freebytes] = processInfoForSingleEvacPage(allocator->evacpage, pendingdeletes);
        stat.livebytes += livebytes;
        stat.freebytes += freebytes;
    }

    void processInfoForPageSetEntries(const GCAllocatorImpl* allocator, HeapStats& stat, const std::unordered_set<void*>& pendingdeletes)
    {
        stat.totalpages += allocator->pageset.size();

        for(auto iter = allocator->pageset.begin(); iter != allocator->pageset.end(); iter++) {
            auto [livebytes, freebytes] = processInfoForSinglePage(*iter, stat.pagesetutilizations, pendingdeletes);
            stat.livebytes += livebytes;
            stat.freebytes += freebytes;
        }

        stat.overallutilizations.count_0_30 += stat.pagesetutilizations.count_0_30;
        stat.overallutilizations.count_30_70 += stat.pagesetutilizations.count_30_70;
        stat.overallutilizations.count_70_100 += stat.pagesetutilizations.count_70_100;
    }

    void processAllocatorInfo(const GCAllocatorImpl* allocator, HeapStats& stat, const std::unordered_set<void*>& pendingdeletes, const std::unordered_set<void*>& allpages)
    {
        if(allocator->evacpage != nullptr) {
            assert(std::find(allocator->hot_nursery_pages.begin(), allocator->hot_nursery_pages.end(), allocator->evacpage) == allocator->hot_nursery_pages.end());
            assert(std::find(allocator->pageset.begin(), allocator->pageset.end(), allocator->evacpage) == allocator->pageset.end());

            assert(allocator->evacpage->typeinfo == allocator->alloctype);
            assert(allocator->evacpage->gcalloc == allocator);

            assert(allpages.contains(allocator->evacpage));
        }

        for(auto iter = allocator->hot_nursery_pages.begin(); iter != allocator->hot_nursery_pages.end(); iter++) {
            assert(std::find(allocator->pageset.begin(), allocator->pageset.end(), *iter) == allocator->pageset.end());

            assert((*iter)->typeinfo == allocator->alloctype);
            assert((*iter)->gcalloc == allocator);

            assert(allpages.contains(*iter));
        }

        for(auto iter = allocator->pageset.begin(); iter != allocator->pageset.end(); iter++) {
            assert(std::find(allocator->hot_nursery_pages.begin(), allocator->hot_nursery_pages.end(), *iter) == allocator->hot_nursery_pages.end());

            assert((*iter)->typeinfo == allocator->alloctype);
            assert((*iter)->gcalloc == allocator);

            assert(allpages.contains(*iter));
        }

        processInfoForHotNurseryPages(allocator, stat, pendingdeletes);
        processInfoForActiveEvacPage(allocator, stat, pendingdeletes);
        processInfoForPageSetEntries(allocator, stat, pendingdeletes);
    }

    void processAllAllocatorsInfo(const std::map<uint32_t, GCAllocatorImpl*>& gcallocs, HeapStats& stat)
    {
        std::unordered_set<void*> pendingdeletes;
        for(auto iter = tl_alloc_info.pendingdelete.cbegin(); iter != tl_alloc_info.pendingdelete.cend(); iter++) {
            pendingdeletes.insert(*iter);
        }

        for(auto iter = g_alloc_info.allocatedpages.cbegin(); iter != g_alloc_info.allocatedpages.cend(); iter++) {
            assert(g_alloc_info.minpageaddr <= (uintptr_t)(*iter));
            assert((uintptr_t)(*iter) < g_alloc_info.maxpageaddr);
        }

        for(auto iter = gcallocs.begin(); iter != gcallocs.end(); iter++) {
            processAllocatorInfo(iter->second, stat, pendingdeletes, g_alloc_info.allocatedpages);
        }
    }

    void gcValidate()
    {
        g_memstats.advanceHeapStats();
        processAllAllocatorsInfo(tl_alloc_info.gcallocs, g_memstats.getCurrentHeapStats());
    }
}

#pragma once

#include "xalloc.h"

#define NUM_VADDR_BITS 48
#define PAGE_PRESENT (reinterpret_cast<void*>(1))
#define LAST_LEVEL 1

//A class that keeps track of which pages are in use in the GC
class PageTable {
    void** root;
    size_t entriesPerPage;
    size_t numAddrBitsForLevel;
    size_t numLevels;
    size_t levelMask;

    inline size_t determineAddrBits() const noexcept {
        size_t v = this->entriesPerPage;
        size_t c = 0;
        while(v > 1) {
            v >>= 1;
            c++;
        }
        return c;
    }

    inline size_t determineNumLevels() const noexcept {
        size_t bitsForPages = NUM_VADDR_BITS - BITS_IN_ADDR_FOR_PAGE;
        return (bitsForPages + this->numAddrBitsForLevel - 1) / this->numAddrBitsForLevel;
    }

public:
    PageTable(): root(nullptr), entriesPerPage(0), numAddrBitsForLevel(0), 
                 numLevels(0), levelMask(0)
    {
        this->root = static_cast<void**>(XAllocPageManager::g_page_manager.allocatePage());
        xmem_zerofillpage(this->root);

        this->entriesPerPage = BSQ_BLOCK_ALLOCATION_SIZE / 8ul;
        this->numAddrBitsForLevel = determineAddrBits();
        this->numLevels = determineNumLevels();
        this->levelMask = (1 << this->numAddrBitsForLevel) - 1;
    }

    void insert(void* addr) noexcept 
    {
		std::lock_guard lk(g_gcmemlock);

        uintptr_t naddr = reinterpret_cast<uintptr_t>(addr);
        void** level = this->root;
        
        for(size_t i = this->numLevels; i > 0; i--) {
            size_t shift = BITS_IN_ADDR_FOR_PAGE + (i - 1) * this->numAddrBitsForLevel;
            size_t pageidx = (naddr >> shift) & this->levelMask;
            
            if(i == LAST_LEVEL) {
                DSA_INVARIANT_CHECK(level[pageidx] == nullptr);
                
                level[pageidx] = PAGE_PRESENT;
            } 
            else {
                if(!level[pageidx]) {
                    level[pageidx] = static_cast<void**>(XAllocPageManager::g_page_manager.allocatePage());
                    xmem_zerofillpage(level[pageidx]);
                }

                level = static_cast<void**>(level[pageidx]);
            }
        }
    }

    bool query(void* addr) noexcept
    {
		std::lock_guard lk(g_gcmemlock);

        uintptr_t naddr = reinterpret_cast<uintptr_t>(addr);
        void** level = this->root;
        
        for(size_t i = this->numLevels; i > 0; i--) {
            size_t shift = BITS_IN_ADDR_FOR_PAGE + (i - 1) * this->numAddrBitsForLevel;
            size_t pageidx = (naddr >> shift) & this->levelMask;
            
            if(i == LAST_LEVEL) {
                DSA_INVARIANT_CHECK(level[pageidx] == PAGE_PRESENT || level[pageidx] == nullptr);

                return level[pageidx] == PAGE_PRESENT;
            } 
            else {
                if(!level[pageidx]) {
                    return false;
                }

                level = static_cast<void**>(level[pageidx]);
            }
        }
        
        return false;
    }
};

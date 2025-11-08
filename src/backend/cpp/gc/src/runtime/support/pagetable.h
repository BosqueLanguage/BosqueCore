#pragma once

#include "xalloc.h"

#define NUM_VADDR_BITS 48

//A class that keeps track of which pages are in use in the GC
class PageTable {
    void** root;

    size_t entriesPerPage; // e.g., 512, 1024, ...
    size_t numAddrBitsForLevel; // e.g. 8, 9, 10...
    size_t numLevels;
    size_t numLastLevelBits; // Special case for handling varried page sizes

    inline size_t determineAddrBits() const noexcept {
        size_t v = this->entriesPerPage - 1; // Always power of two so invert
        size_t c;
        for (c = 0; v; c++) {
            v &= v - 1; // Clear the least significant bit set
        }

        return c;
    }

    inline size_t determineNumLevels() const noexcept {
        size_t addrbits = NUM_VADDR_BITS;
        size_t nlevels = 0;
        while(addrbits > BITS_IN_ADDR_FOR_PAGE) {
            addrbits -= this->numAddrBitsForLevel;
            nlevels++;
        }

        return nlevels;
    }

    inline size_t determineNumLastLevelBits() const noexcept {
        size_t levelbits = this->numAddrBitsForLevel * this->numLevels;
        size_t allbits = levelbits + BITS_IN_ADDR_FOR_PAGE;
        size_t remainder = allbits - NUM_VADDR_BITS;

        return this->numAddrBitsForLevel - remainder;
    }

public:
    PageTable(): root(nullptr), entriesPerPage(0), numAddrBitsForLevel(0), numLevels(0), numLastLevelBits(0)
    {
        this->root = static_cast<void**>(XAllocPageManager::g_page_manager.allocatePage());
        xmem_zerofillpage(this->root);

        this->entriesPerPage = BSQ_BLOCK_ALLOCATION_SIZE / 8ul;
        this->numAddrBitsForLevel = determineAddrBits();
        this->numLevels = determineNumLevels();
        this->numLastLevelBits = determineNumLastLevelBits();
    }

    void insert(void* addr) noexcept 
    {
        uintptr_t naddr = reinterpret_cast<uintptr_t>(addr);
        void** level = this->root;
        for(size_t i = numLevels; i >= 1; i--) {
            size_t pageidx = (naddr >> (this->numAddrBitsForLevel * i));
            if(level[pageidx] == nullptr) {
                level[pageidx] = static_cast<void**>(XAllocPageManager::g_page_manager.allocatePage());
                xmem_zerofillpage(level[pageidx]);
            }

            level = static_cast<void**>(level[pageidx]);
        }

        size_t pageidx = naddr >> this->numLastLevelBits;
        void* e = level[pageidx];
        DSA_INVARIANT_CHECK(e == nullptr);
    
        level[pageidx] = addr;
    }

    bool query(void* addr) noexcept
    {
        uintptr_t naddr = reinterpret_cast<uintptr_t>(addr);
        void** level = this->root;
        for(size_t i = numLevels; i >= 1; i--) {
            size_t pageidx = (naddr >> (this->numAddrBitsForLevel * i));
            if(level[pageidx] == nullptr) {
                return false;
            }

            level = static_cast<void**>(level[pageidx]);
        }

        size_t pageidx = naddr >> this->numLastLevelBits;
        return level[pageidx] != nullptr;
    } 
};

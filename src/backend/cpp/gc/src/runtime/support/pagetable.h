#pragma once

#include "xalloc.h"

#define PAGETABLE_LEVELS 4
#define BITS_PER_LEVEL   9 

#define LEVEL1_SHIFT 39 
#define LEVEL2_SHIFT 30 
#define LEVEL3_SHIFT 21 
#define LEVEL4_SHIFT 12 

#define LEVEL_MASK 0x1FFUL 
#define PAGE_MASK  0xFFFUL

#define PAGE_PRESENT 1

//A class that keeps track of which pages are in use in the GC
class PageTableInUseInfo
{
private:
    void** pagetable_root;
public:
    PageTableInUseInfo() noexcept : pagetable_root(nullptr) {}

    void pagetable_insert(void* addr) noexcept {
        if(this->pagetable_root == nullptr) {
            this->pagetable_root = (void**)XAllocPageManager::g_page_manager.allocatePage();
            xmem_zerofillpage(this->pagetable_root);
        }

        uintptr_t address = (uintptr_t)addr;
        uintptr_t index1 = (address >> LEVEL1_SHIFT) & LEVEL_MASK; // Bits 47-39
        uintptr_t index2 = (address >> LEVEL2_SHIFT) & LEVEL_MASK; // Bits 38-30
        uintptr_t index3 = (address >> LEVEL3_SHIFT) & LEVEL_MASK; // Bits 29-21
        uintptr_t index4 = (address >> LEVEL4_SHIFT) & LEVEL_MASK; // Bits 20-12

        void** level1 = pagetable_root;
        if(!level1[index1]) {
            level1[index1] = (void**)XAllocPageManager::g_page_manager.allocatePage();
            xmem_zerofillpage(level1[index1]);
        }

        void** level2 = (void**)level1[index1];
        if(!level2[index2]) {
            level2[index2] = (void**)XAllocPageManager::g_page_manager.allocatePage();
            xmem_zerofillpage(level2[index2]);
        }

        void** level3 = (void**)level2[index2];
        if(!level3[index3]) {
            level3[index3] = (void**)XAllocPageManager::g_page_manager.allocatePage();
            xmem_zerofillpage(level3[index3]);
        }

        void** level4 = (void**)level3[index3];
        level4[index4] = (void*)PAGE_PRESENT;  
    }

    bool pagetable_query(void* addr) const noexcept {
        if(this->pagetable_root == nullptr) {
            return false;
        }
        
        uintptr_t address = (uintptr_t)addr;
        uintptr_t index1 = (address >> LEVEL1_SHIFT) & LEVEL_MASK; // Bits 47-39
        uintptr_t index2 = (address >> LEVEL2_SHIFT) & LEVEL_MASK; // Bits 38-30
        uintptr_t index3 = (address >> LEVEL3_SHIFT) & LEVEL_MASK; // Bits 29-21
        uintptr_t index4 = (address >> LEVEL4_SHIFT) & LEVEL_MASK; // Bits 20-12

        void** level1 = pagetable_root;
        if(!level1[index1]) {
            return false;
        }

        void** level2 = (void**)level1[index1];
        if(!level2[index2]) {
            return false;
        }

        void** level3 = (void**)level2[index2];
        if(!level3[index3]) {
            return false;
        }

        void** level4 = (void**)level3[index3];
        return level4[index4] == (void*)PAGE_PRESENT;
    }
};


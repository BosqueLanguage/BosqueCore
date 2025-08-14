#pragma once

///////////////////////////////////
// Epsilon Allocator 
// -- Does no memory management what so ever, continues to allocate BSQ_BLOCK_ALLOCATION_SIZE pages until OOM (so be careful!)
// -- Intended to aid with observing GC impact on performance 
// -- Enabled by running make with `ALLOC=epsilon` (e.g. `make BUILD=release ALLOC=epsilon`)

#ifdef EPSILON 

#include "../common.h"

class EpsilonAllocator {
private: 
    void* ptr;
    
    void* heapstart;
    void* current;
    void* heapend;

    // Append new page onto current, then bump heapend pointer to reflect new block
    void allocatePage() noexcept {
#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
        if(current == nullptr) {
            this->current = ALLOC_BASE_ADDRESS;
        }
        else {
            this->current = static_cast<uint8_t*>(this->current) + BSQ_BLOCK_ALLOCATION_SIZE;
        }

        this->current = mmap(this->current, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0);
#else
        this->current = mmap(NULL, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);

        if(this->heapstart == nullptr) {
            this->heapstart = this->current;
        }
#endif
        if(this->ptr == nullptr) {
            this->ptr = this->current;
        }

        if(this->current == MAP_FAILED) {
            this->freeheap();
            assert(false);
        }

        this->heapend = static_cast<uint8_t*>(this->current) + BSQ_BLOCK_ALLOCATION_SIZE;
    }

#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
    EpsilonAllocator() noexcept : ptr(ALLOC_BASE_ADDRESS), heapstart(ALLOC_BASE_ADDRESS), current(nullptr), heapend(ALLOC_BASE_ADDRESS) {}
#else 
    EpsilonAllocator() noexcept : ptr(nullptr), heapstart(nullptr), current(nullptr), heapend(nullptr) {}
#endif
public:
    static EpsilonAllocator alloc;

    // Get a new block of tinfo->type_size from heap
    inline void* allocate(__CoreGC::TypeInfoBase* tinfo)
    {
        if(static_cast<uint8_t*>(ptr) + tinfo->type_size > heapend || ptr == nullptr) [[unlikely]] {
            this->allocatePage();
        }
        
        void* entry = this->ptr;
        this->ptr = static_cast<uint8_t*>(this->ptr) + tinfo->type_size;
    
        return entry;
    }

    // Frees all memory from heapstart -> heapend (this may not get used)
    void freeheap() noexcept
    {
        munmap(heapstart, static_cast<uintptr_t*>(heapstart) - static_cast<uintptr_t*>(heapend));
    }
};

#else
#endif //EPSILON
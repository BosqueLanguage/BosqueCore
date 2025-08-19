#pragma once

///////////////////////////////////
// Epsilon Allocator 
// -- Does no memory management what so ever, continues to allocate 1 GB pages until OOM (so be careful!)
// -- Intended to aid with observing GC impact on performance 
// -- Enabled by running make with `ALLOC=epsilon` (e.g. `make BUILD=release ALLOC=epsilon`)

#ifdef EPSILON 

#include "../common.h"

// 1 GB
#define EPSILON_BLOCK_SIZE (1024UL * 1024UL * 1024UL)
#define GET_PAGE_END(P) (reinterpret_cast<uint8_t*>(P) + EPSILON_BLOCK_SIZE)

struct EpsilonPage {
    EpsilonPage* next;
};

class EpsilonAllocator {
private: 
    void* ptr;
    EpsilonPage* allpages;
    EpsilonPage* curpage;

#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
    void* curaddr;
#else
#endif

    void allocatePage() noexcept {
#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
        EpsilonPage* page = static_cast<EpsilonPage*>(mmap(curaddr, EPSILON_BLOCK_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0));
        curaddr = static_cast<uint8_t*>(curaddr) + EPSILON_BLOCK_SIZE;
#else
        EpsilonPage* page = static_cast<EpsilonPage*>(mmap(NULL, EPSILON_BLOCK_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0));
#endif
        if(page == MAP_FAILED) [[unlikely]] {
            this->freeheap();
            assert(false);
        }

        if(this->curpage == nullptr) [[unlikely]] {
            this->curpage = page;   
        }
        else {
            this->curpage->next = page;
            this->curpage = this->curpage->next;
        }
        this->curpage->next = nullptr;

        if(this->allpages == nullptr) [[unlikely]] {
            this->allpages = this->curpage;
        }

        this->ptr = reinterpret_cast<uint8_t*>(this->curpage) + sizeof(EpsilonPage);
    }

#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
    EpsilonAllocator() noexcept : ptr(nullptr), allpages(nullptr), curpage(nullptr), curaddr(ALLOC_BASE_ADDRESS) {}
#else 
    EpsilonAllocator() noexcept : ptr(nullptr), allpages(nullptr), curpage(nullptr) {}
#endif

public:
    static EpsilonAllocator alloc;

    // Get a new block of tinfo->type_size from heap
    inline void* allocate(__CoreGC::TypeInfoBase* tinfo) {
        void* next = static_cast<uint8_t*>(this->ptr) + tinfo->type_size; 
        if (this->curpage == nullptr || next > GET_PAGE_END(this->curpage)) [[unlikely]] {
            this->allocatePage();
            next = static_cast<uint8_t*>(this->ptr) + tinfo->type_size;  // Recalculate after new page
        }
    
        void* entry = this->ptr;
        this->ptr = next;

        return entry;
    }

    void freeheap() noexcept
    {
        EpsilonPage* p = this->allpages;
        while(p != nullptr) {
            EpsilonPage* next = p->next;
            munmap(p, EPSILON_BLOCK_SIZE);

            p = next;
        }
    }
};

#else
#endif //EPSILON
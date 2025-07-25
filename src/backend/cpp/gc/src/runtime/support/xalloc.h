
/**
 * This is the memory allocator that we will use for MANUALLY manged (NON-GC) memory that we need when implementing the GC itself and other runtime support.
 * At this point it supports a pool of pages and allocation from this pool.
 * 
 * This is a thread local (static) allocator.
 */
#pragma once

#include "../common.h"

struct XAllocPage {
    XAllocPage* next;
};

//This class is responsible for managing the allocation of pages for support data structures (NOT GC pages)
//All threads will share this pool of pages for their operations (locked by a global mutex ALLOC_LOCK_X operations)
class XAllocPageManager
{
private:
    XAllocPage* freelist;

    void* allocatePage_impl() noexcept;
    void freePage_impl(void* page) noexcept;

    XAllocPageManager() noexcept : freelist(nullptr) {}
public:
    static XAllocPageManager g_page_manager;

    void* allocatePage() noexcept
    {
        return this->allocatePage_impl();
    }

    void freePage(void* page) noexcept
    {
        this->freePage_impl((void*)page);
    }
};


#include "xalloc.h"

XAllocPageManager XAllocPageManager::g_page_manager;

void* XAllocPageManager::allocatePage_impl() noexcept
{
    ALLOC_LOCK_ACQUIRE();
    
    if(this->freelist == NULL)
    {
#ifndef ALLOC_DEBUG_MEM_DETERMINISTIC
        this->freelist = (XAllocPage*)mmap(NULL, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
#else
        this->freelist = (XAllocPage*)mmap(GlobalThreadAllocInfo::s_current_page_address, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0);
        GlobalThreadAllocInfo::s_current_page_address = (void*)((uint8_t*)GlobalThreadAllocInfo::s_current_page_address + BSQ_BLOCK_ALLOCATION_SIZE);
#endif
        assert(this->freelist != MAP_FAILED);

#ifdef ALLOC_DEBUG_MEM_INITIALIZE
        xmem_zerofillpage(this->freelist);
#endif

        this->freelist->next = NULL;
    }

    XAllocPage* xpage = this->freelist;
    this->freelist = this->freelist->next;

    ALLOC_LOCK_RELEASE();

    return (void*)xpage;
}

void XAllocPageManager::freePage_impl(void* page) noexcept
{
    XAllocPage* xpage = (XAllocPage*)page;

#ifdef ALLOC_DEBUG_MEM_INITIALIZE
    xmem_zerofillpage(xpage);
#endif

    ALLOC_LOCK_ACQUIRE();
    xpage->next = this->freelist;
    this->freelist = xpage;
    ALLOC_LOCK_RELEASE();
}
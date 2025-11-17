#include "common.h"

mtx_t g_alloclock;
mtx_t g_gcmemlock;
mtx_t g_gcrefctlock;

size_t GlobalThreadAllocInfo::s_thread_counter = 0;

#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
void* GlobalThreadAllocInfo::s_current_page_address = ALLOC_BASE_ADDRESS;
#else 
#endif
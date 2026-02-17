#include "common.h"

std::mutex g_alloclock;
std::mutex g_gcmemlock;
std::mutex g_gcrefctlock;
std::mutex g_gctelemetrylock;

size_t GlobalThreadAllocInfo::s_thread_counter = 0;

#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
void* GlobalThreadAllocInfo::s_current_page_address = ALLOC_BASE_ADDRESS;
#endif

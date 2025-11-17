#pragma once

#ifdef GC_INVARIANTS
#define GC_INVARIANT_CHECK(x) assert(x)
#else
#define GC_INVARIANT_CHECK(x)
#endif

//This methods drives the collection routine -- uses the thread local information from invoking thread to get pages 
extern void collect() noexcept;

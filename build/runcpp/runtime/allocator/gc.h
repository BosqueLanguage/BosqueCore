#pragma once

#include "alloc.h"

namespace ᐸRuntimeᐳ
{
    //These methods drives the collection routine -- uses the thread local information from invoking thread to get pages
    void processPendingDeleteWork(size_t worklimit);
    void collect();

#ifdef GC_TESTING
    void test_collect(std::initializer_list<void*> roots);
#endif
}
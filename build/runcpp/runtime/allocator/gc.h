#pragma once

#include "alloc.h"

namespace ᐸRuntimeᐳ
{
    //These methods drives the collection routine -- uses the thread local information from invoking thread to get pages
    void processPendingDeleteWork(GCAllocatorImpl* alloc);
    void collect();
}
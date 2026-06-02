#pragma once

#include "alloc.h"

namespace ᐸRuntimeᐳ
{
    //This methods drives the collection routine -- uses the thread local information from invoking thread to get pages
    void collect();
}
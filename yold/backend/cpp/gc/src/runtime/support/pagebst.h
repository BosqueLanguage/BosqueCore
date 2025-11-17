#pragma once

#include "../memory/allocator.h"

///////////////////////////////////
// Binary Search Tree For Pages
// - Allows us to retrieve pages based on approximate utilization 
//   from their respective allocator
// - Designed to be used with buckets of pages
// - If we notice these trees becoming unbalanced very often
//   we should incorperate rotations

bool insertPageInBucket(GCAllocator* alloc, PageInfo* p);

PageInfo* getLowestUtilPageLow(GCAllocator* alloc) noexcept;
PageInfo* getLowestUtilPageHigh(GCAllocator* alloc) noexcept;
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
bool insertPageLow(GCAllocator* alloc, PageInfo* p);
bool insertPageHigh(GCAllocator* alloc, PageInfo* p);
PageInfo* insert(PageInfo* cur, PageInfo* entry) noexcept;

PageInfo* getLowestUtilPageLow(GCAllocator* alloc) noexcept;
PageInfo* getLowestUtilPageHigh(GCAllocator* alloc) noexcept;
PageInfo* getLowestUtilPageAndRemove(PageInfo* cur, PageInfo** lowest) noexcept;
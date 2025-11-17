#include "../common.h"
#include "pagebst.h"

#define IS_LOW_UTIL(U) (U >= 0.01f && U <= 0.60f)
#define IS_HIGH_UTIL(U) (U > 0.60f && U <= 0.90f)

#define UTILIZATIONS_ARE_EQUAL(F1, F2) (-0.00001 <= (F1 - F2) && (F1 - F2) <= 0.00001)

#define NO_BUCKET_FOUND -1

static PageInfo* insert(PageInfo* cur, PageInfo* entry) noexcept 
{
    if(cur == nullptr) {
        return entry;
    }

    float cutil = cur->approx_utilization;
    float eutil = entry->approx_utilization;
    if(UTILIZATIONS_ARE_EQUAL(cutil, eutil)) {
        entry->next = cur;
        return entry;
    }
    else if(eutil < cutil) {
        cur->left = insert(cur->left, entry);
    }
    else {
        cur->right = insert(cur->right, entry);
    }

    return cur;
}

static inline int getBucketIndex(float util, int nbuckets, bool ishighutil) noexcept 
{
    float tmp_util = 0.0f;
    if(ishighutil) {
        tmp_util = 0.60f;
    }
    
    for(int i = 0; i < nbuckets; i++) {
        float new_tmp_util = tmp_util + 0.05f;
        if (util > tmp_util && util <= new_tmp_util) {
            return i;
        }
        tmp_util = new_tmp_util;
    }

    return NO_BUCKET_FOUND;
}

static bool insertPageLow(GCAllocator* alloc, PageInfo* p) 
{
    float util = p->approx_utilization;
    if(!IS_LOW_UTIL(util)) {
        return false;
    }

    int idx = getBucketIndex(util, NUM_LOW_UTIL_BUCKETS, false);
    if(idx == NO_BUCKET_FOUND) {
        // If page is low util but no idx found something failed
        assert(false);
    }

    PageInfo* root = alloc->low_util_buckets[idx];
    alloc->low_util_buckets[idx] = insert(root, p);

    return true;
}

static bool insertPageHigh(GCAllocator* alloc, PageInfo* p) 
{
    float util = p->approx_utilization;
    if(!IS_HIGH_UTIL(util)) {
        return false;
    }

    int idx = getBucketIndex(util, NUM_HIGH_UTIL_BUCKETS, true);
    if(idx == NO_BUCKET_FOUND) {
        // If page is high util but no idx found something failed
        assert(false);
    }
    
    PageInfo* root = alloc->high_util_buckets[idx];
    alloc->high_util_buckets[idx] = insert(root, p);

    return true;
}

bool insertPageInBucket(GCAllocator* alloc, PageInfo* p) 
{
    if(insertPageLow(alloc, p)) {
        return true;
    }

    if(insertPageHigh(alloc, p)) {
        return true;
    }

    return false;
}

static inline PageInfo* resetPointers(PageInfo* p) noexcept 
{
    if(p == nullptr) {
        return nullptr;
    }

    p->next = nullptr;
    p->left = nullptr;
    p->right = nullptr;

    return p;
}

template<int N>
static inline int findFirstBucket(PageInfo* buckets[N]) noexcept 
{
    int idx = 0;
    while (idx < N) {
        if(buckets[idx] != nullptr) {
            break;
        }
        idx++;
    }

    if(idx == N) {
        return NO_BUCKET_FOUND;
    }
    
    return idx;
}

static PageInfo* getLowestUtilPageAndRemove(PageInfo* cur, PageInfo** lowest) noexcept
{
    if(cur->left == nullptr) {
        *lowest = cur;
        if(cur->next != nullptr) {
            PageInfo* replacement = cur->next;
            replacement->right = cur->right;
            return replacement;
        }
    
        return cur->right;
    }

    cur->left = getLowestUtilPageAndRemove(cur->left, lowest);
    return cur;
}

PageInfo* getLowestUtilPageLow(GCAllocator* alloc) noexcept 
{
    int idx = findFirstBucket<NUM_LOW_UTIL_BUCKETS>(alloc->low_util_buckets);
    if(idx == NO_BUCKET_FOUND) {
        return nullptr;
    }

    PageInfo* lowest = nullptr;
    PageInfo* nroot = getLowestUtilPageAndRemove(alloc->low_util_buckets[idx], &lowest);
    alloc->low_util_buckets[idx] = nroot;

    assert(lowest != nullptr);

    return resetPointers(lowest);
}

PageInfo* getLowestUtilPageHigh(GCAllocator* alloc) noexcept 
{
    int idx = findFirstBucket<NUM_HIGH_UTIL_BUCKETS>(alloc->high_util_buckets);
    if(idx == NO_BUCKET_FOUND) {
        return nullptr;
    }
 
    PageInfo* lowest = nullptr;
    PageInfo* nroot = getLowestUtilPageAndRemove(alloc->high_util_buckets[idx], &lowest);
    alloc->high_util_buckets[idx] = nroot;

    assert(lowest != nullptr);

    return resetPointers(lowest);
}
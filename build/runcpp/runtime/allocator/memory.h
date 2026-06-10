#pragma once

#include "../../common.h"
#include "../../core/bsqtype.h"

#include "memstats.h"

#if BSQ_ALLOCATOR_USE_MALLOC
#ifndef GC_NURSERY_SIZE
#define GC_NURSERY_SIZE 2
//#define GC_NURSERY_SIZE 2048
#endif
#endif

//Make sure any allocated page is addressable by us -- larger than 2^31 and less than 2^42
#define GC_MIN_ALLOCATED_ADDRESS ((void*)(2147483648ul))
#define GC_MAX_ALLOCATED_ADDRESS ((void*)(281474976710656ul))

#define GC_MEM_ALIGNMENT 8

//Control for page sizes and access
#define GC_BITS_IN_ADDR_FOR_PAGE 13ul
#define GC_PAGE_SIZE (1ul << GC_BITS_IN_ADDR_FOR_PAGE)
#define GC_BLOCK_ALLOCATION_SIZE (1ul << GC_BITS_IN_ADDR_FOR_PAGE)
#define GC_PAGE_MASK ((1ul << GC_BITS_IN_ADDR_FOR_PAGE) - 1ul)
#define GC_PAGE_ADDR_MASK (~GC_PAGE_MASK)

//A bunch of knobs for adjusting GC behavior -- these are all subject to tuning as with the page info above
#define GC_NUM_PAGES_ON_REQ 16
#define GC_NUSERY_BYTES_COLLECT_THRESHOLD (1ul << 23)
#define GC_DELETE_PENDING_PROCESS_BYTES (GC_NUSERY_BYTES_COLLECT_THRESHOLD / 20)

namespace ᐸRuntimeᐳ
{
    using GCMetaBits = uint64_t;
    using AtomicGCMetadata = std::atomic<GCMetaBits>;

    static_assert(sizeof(void*) == 8, "This GC implementation assumes 64 bit pointers for the bit packing to work correctly");
    static_assert(sizeof(GCMetaBits) == 8, "This GC implementation assumes 64 bit pointers for the bit packing to work correctly");
    static_assert(sizeof(AtomicGCMetadata) == 8, "AtomicGCMetadata must be 8 bytes for bit packing to work correctly");

    //These bits are monotone in the lifecycle of an allocation 
    constexpr GCMetaBits META_BIT_IS_ALLOC = 0x1;
    constexpr GCMetaBits META_BIT_IS_YOUNG = 0x2;
    constexpr GCMetaBits META_BIT_IS_FORWARD = 0x4;
    constexpr GCMetaBits META_BIT_IS_RC_UNIQUE = 0x10;
    constexpr GCMetaBits META_BIT_IS_RC_SHARED = 0x20;
    constexpr GCMetaBits META_BIT_IS_DELETE_PENDING = 0x40;

    constexpr GCMetaBits META_BIT_RC_ZERO = 0x0;
    constexpr GCMetaBits META_BIT_RC_ONE = 0x80;
    constexpr GCMetaBits META_BIT_RC_TWO = (META_BIT_RC_ONE + META_BIT_RC_ONE);
    constexpr GCMetaBits META_BIT_RC_MASK = ~(0x7F);
    constexpr uint32_t META_BIT_RC_ADDR_SHIFT = 4; //bottom 3 bits are zero already based on alignment
    constexpr uint32_t META_BIT_RC_FREELIST_SHIFT = 7; //same as above but all bits moved

    constexpr uint16_t META_FREE_LIST_OOM_SENTINAL = 0xFFFF;

    constexpr bool gcIsAllocated(const AtomicGCMetadata* rc) 
    {
        return (rc->load(std::memory_order_relaxed) & META_BIT_IS_ALLOC) != 0;
    }

    constexpr bool gcIsYoung(const AtomicGCMetadata* rc) 
    {
        return (rc->load(std::memory_order_relaxed) & META_BIT_IS_YOUNG) != 0;
    }

    constexpr bool gcIsForwarded(const AtomicGCMetadata* rc) 
    {
        return (rc->load(std::memory_order_relaxed) & META_BIT_IS_FORWARD) != 0;
    }

    constexpr bool gcIsRC(const AtomicGCMetadata* rc) 
    {
        return (rc->load(std::memory_order_relaxed) & (META_BIT_IS_RC_UNIQUE | META_BIT_IS_RC_SHARED)) != 0;
    }

    //Set the state on initial allocation into the nursery
    constexpr void gcInitOnAllocate(AtomicGCMetadata* rc)
    {
        rc->store(META_BIT_IS_ALLOC | META_BIT_IS_YOUNG, std::memory_order_relaxed);
    }

    //Set the state on allocation for an evacuation target -- the unique RC bit to indicate that there is a unique (known addr) heap reference
    constexpr void gcInitOnEvacuate(AtomicGCMetadata* rc, void** addr)
    {
        rc->store(META_BIT_IS_ALLOC | META_BIT_IS_RC_UNIQUE | ((uintptr_t)addr << META_BIT_RC_ADDR_SHIFT), std::memory_order_relaxed);
    }

    constexpr bool gcRootProcessRCIncrement(AtomicGCMetadata* rc)
    {
        //on root increment this could be a "forged" reference 
        //so we CAS to make sure we aren't incrementing something that isn't already a valid RC object
        //we hold page mutex so we know the memory location is otherwise valid
        //return true if we successfully incremented, false if this is a TOCTOU or forged reference

        GCMetaBits ll = rc->load(std::memory_order_relaxed);
        while(true) {
            if(((ll & META_BIT_RC_MASK) == 0) | ((ll & META_BIT_IS_DELETE_PENDING) != 0)) {
                return false;
            }

            GCMetaBits newbits;
            if(ll & META_BIT_IS_RC_UNIQUE) {
                //Was a unique reference but we need to clear this and set the counter correctly (to 2)
                newbits = (META_BIT_IS_ALLOC | META_BIT_IS_RC_SHARED | META_BIT_RC_TWO);
                
            }
            else {
                //Otherwise just increment the counter
                newbits = ll + META_BIT_RC_ONE;
            }

            if(rc->compare_exchange_weak(ll, newbits)) {
                return true;
            }
        }
    }

    //The object is now a forward object -- so allocated and keep young so we know to collect it when sweeping (moved to the forwarding state)
    constexpr void gcProcessUpdateYoungForward(AtomicGCMetadata* rc)
    {
        rc->store(META_BIT_IS_ALLOC | META_BIT_IS_YOUNG | META_BIT_IS_FORWARD, std::memory_order_relaxed);
    }

    //The object is pointed to by a root of some kind, so cant unique parent it, just set the RC to 1
    constexpr void gcRootProcessYoungPromote(AtomicGCMetadata* rc)
    {
        rc->store(META_BIT_IS_ALLOC | META_BIT_IS_RC_SHARED | META_BIT_RC_ONE, std::memory_order_relaxed);
    }

    //Increment the RC from a non-root reference -- these references area always precise to just increment in the appropriate way
    constexpr void gcYoungProcessRCIncrement(AtomicGCMetadata* rc)
    {
        GCMetaBits ll = rc->load(std::memory_order_relaxed);
        while(true) {
            GCMetaBits newbits;
            if(ll & META_BIT_IS_RC_UNIQUE) {
                //Was a unique reference but we need to set the counter correctly (to 2)
                newbits = (META_BIT_IS_ALLOC | META_BIT_IS_RC_SHARED | META_BIT_RC_TWO);
            }
            else {
                //Otherwise just increment the counter
                newbits = ll + META_BIT_RC_ONE;
            }

            if(rc->compare_exchange_weak(ll, newbits)) {
                break;
            }
        }
    }

    //Decrement the RC and set to delete pending if we hit zero -- return true if we hit zero and need to process false otherwise
    constexpr bool gcProcessRCDecrement(AtomicGCMetadata* rc)
    {
        GCMetaBits ll = rc->load(std::memory_order_relaxed);
        while(true) {
            GCMetaBits newbits;
            if(ll & META_BIT_IS_RC_UNIQUE) {
                //Was a unique reference but now delete pending
                newbits = (META_BIT_IS_ALLOC | META_BIT_IS_DELETE_PENDING | META_BIT_RC_ZERO);
            }
            else {
                //Otherwise just increment the counter
                if((ll & META_BIT_RC_MASK) == META_BIT_RC_ONE) {
                    //This decrement would put us at zero, so set delete pending
                    newbits = (META_BIT_IS_ALLOC | META_BIT_IS_DELETE_PENDING | META_BIT_RC_ZERO);
                }
                else {
                    newbits = ll - META_BIT_RC_ONE;
                }
            }

            if(rc->compare_exchange_weak(ll, newbits)) {
                return (newbits & META_BIT_IS_DELETE_PENDING) != 0;
            }
        }
    }

    //Thread the pending delete freelist via the rc counter
    constexpr void gcStoreDeleteListPtr(AtomicGCMetadata* rc, void* addr)
    {
        GCMetaBits ll = rc->load(std::memory_order_relaxed);
        rc->store(ll | ((uintptr_t)addr << META_BIT_RC_ADDR_SHIFT), std::memory_order_relaxed);
    }

    //Thread the pending delete freelist via the rc counter
    constexpr void* gcGetDeleteListPtr(AtomicGCMetadata* rc)
    {
        GCMetaBits ll = rc->load(std::memory_order_relaxed);
        return (void*)((ll & META_BIT_RC_MASK) >> META_BIT_RC_ADDR_SHIFT);
    }

    //After processing an object (in sweep or RC deletion) clear the meta bits
    constexpr void gcProcessSweep(AtomicGCMetadata* rc)
    {
        rc->store(0, std::memory_order_relaxed);
    }

    //RC_ADDR bits in freelist entries are nextoffset index values
    constexpr static void gcSetFreeListBits(AtomicGCMetadata* rc, uint16_t nextoffset) {
        rc->store((uint64_t)nextoffset << META_BIT_RC_FREELIST_SHIFT, std::memory_order_relaxed);
    }

    //return the next offset or OOM sentinal for empty
    constexpr static uint16_t gcLoadFreeListNext(const AtomicGCMetadata* rc) {
        return (uint16_t)(rc->load(std::memory_order_relaxed) >> META_BIT_RC_FREELIST_SHIFT);
    }

    struct RegisterContents
    {
        static_assert(__x86_64__, "GC implementation currently only supports x86-64 architecture");

        //Should never have pointers of interest in these
        //void* rbp;
        //void* rsp;

        void* rax = nullptr;
        void* rbx = nullptr;
        void* rcx = nullptr;
        void* rdx = nullptr;
        void* rsi = nullptr;
        void* rdi = nullptr;
        void* r8 = nullptr;
        void* r9 = nullptr;
        void* r10 = nullptr;
        void* r11 = nullptr;
        void* r12 = nullptr;
        void* r13 = nullptr;
        void* r14 = nullptr;
        void* r15 = nullptr;
    };
}

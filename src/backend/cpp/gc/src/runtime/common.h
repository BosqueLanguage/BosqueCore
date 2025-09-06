#pragma once

#include "../language/bsqtype.h"

#include <sys/mman.h> //mmap

//DEFAULT ENABLED WHILE LOTS OF DEVELOPMENT!!!!
#define MEM_STATS
#define BSQ_GC_CHECK_ENABLED
#define VERBOSE_HEADER

#ifdef BSQ_GC_CHECK_ENABLED
#define ALLOC_DEBUG_MEM_INITIALIZE

//
// Note: If we are deterministic the base addresses for our pages
// will be outside of asan's address range. Will need to run asan
// in non-deterministic
//
#define ALLOC_DEBUG_MEM_DETERMINISTIC

#define ALLOC_DEBUG_CANARY
#define DSA_INVARIANTS
#define GC_INVARIANTS
#endif

#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
#define ALLOC_BASE_ADDRESS ((void*)(0x4000000000ul)) 
#define ALLOC_ADDRESS_SPAN 2147483648ul
#endif

#define PAGE_ADDR_MASK 0xFFFFFFFFFFFFF000ul
//Make sure any allocated page is addressable by us -- larger than 2^31 and less than 2^42
#define MIN_ALLOCATED_ADDRESS ((void*)(2147483648ul))
#define MAX_ALLOCATED_ADDRESS ((void*)(281474976710656ul))

#define BSQ_MEM_ALIGNMENT 8
#define BSQ_BLOCK_ALLOCATION_SIZE 4096ul


//
//worst possible case where every entry has to be inserted into fwd table:
//BSQ_BLOCK_ALLOCATION_SIZE / 8 = 512 (assumes every entry is exactly 8 bytes with no padding);
//then BSQ_COLLECTION_THRESHOLD * (BSQ_BLOCK_ALLOCATION_SIZE / 8 ) = 524288, thus max possible
//entries before triggering a collection 
//
#define BSQ_MAX_FWD_TABLE_ENTRIES 524288ul

#define BSQ_MAX_ROOTS 2048ul
#define BSQ_MAX_ALLOC_SLOTS 64ul

//Number of allocation pages we fill up before we start collecting
#define BSQ_COLLECTION_THRESHOLD 1024

//Max number of decrement ops we do per collection -- 
//    TODO:we may need to make this a bit dynamic 
#define BSQ_INITIAL_MAX_DECREMENT_COUNT (BSQ_COLLECTION_THRESHOLD * BSQ_BLOCK_ALLOCATION_SIZE) / (BSQ_MEM_ALIGNMENT * 32)

//mem is an 8byte aligned pointer and n is the number of 8byte words to clear
inline void xmem_zerofill(void* mem, size_t n) noexcept
{
    void** obj = (void**)mem;
    void** end = obj + n;
    while(obj < end) {
        *obj = nullptr;
        obj++;
    }
}

//Clears a page of memory
inline void xmem_zerofillpage(void* mem) noexcept
{
    void** obj = (void**)mem;
    void** end = obj + (BSQ_BLOCK_ALLOCATION_SIZE / sizeof(void*));
    while(obj < end) {
        *obj = nullptr;
        obj++;
    }
}

//mem is an 8byte aligned pointer and n is the number of 8byte words to clear
inline void xmem_copy(void* memsrc, void* memtrgt, size_t n) noexcept
{
    void** objsrc = (void**)memsrc;
    void** objend = objsrc + n;
    void** objtrgt = (void**)memtrgt;
    while(objsrc < objend) {
        *objtrgt = *objsrc;
        objsrc++;
        objtrgt++;
    }
}

//A global mutex lock that all threads will use when accessing shared page lists 
extern mtx_t g_alloclock;

#define ALLOC_LOCK_INIT() assert(mtx_init(&g_alloclock, mtx_plain) == thrd_success)
#define ALLOC_LOCK_ACQUIRE() assert(mtx_lock(&g_alloclock) == thrd_success)
#define ALLOC_LOCK_RELEASE() assert(mtx_unlock(&g_alloclock) == thrd_success)

//A global mutex lock that all threads will use when doing shared GC ops (e.g. getting pages or root resolution)
extern mtx_t g_gcmemlock;

#define GC_MEM_LOCK_INIT() assert(mtx_init(&g_gcmemlock, mtx_plain) == thrd_success)
#define GC_MEM_LOCK_ACQUIRE() assert(mtx_lock(&g_gcmemlock) == thrd_success)
#define GC_MEM_LOCK_RELEASE() assert(mtx_unlock(&g_gcmemlock) == thrd_success)

//A global mutex lock that all threads will use when doing shared GC ops (e.g. when doing their inc/dec ref loops)
extern mtx_t g_gcrefctlock;

#define GC_REFCT_LOCK_INIT() assert(mtx_init(&g_gcrefctlock, mtx_plain) == thrd_success)
#define GC_REFCT_LOCK_ACQUIRE() assert(mtx_lock(&g_gcrefctlock) == thrd_success)
#define GC_REFCT_LOCK_RELEASE() assert(mtx_unlock(&g_gcrefctlock) == thrd_success)

#define INIT_LOCKS() { ALLOC_LOCK_INIT(); GC_MEM_LOCK_INIT(); GC_REFCT_LOCK_INIT(); }

// Track information that needs to be globally accessible for threads
class GlobalThreadAllocInfo
{
public:
    static size_t s_thread_counter;
    static void* s_current_page_address;
    static uint32_t newly_filled_pages_count;

    //TODO: if we need to do deterministic replay we can add a thread page-get buffer here to record/replay from
};

//A handy stack allocation macro
#define BSQ_STACK_ALLOC(SIZE) ((SIZE) == 0 ? nullptr : alloca(SIZE))

/////////////////////////////////////////////
// Packed metadata bit layout
// - All type information needed for the GC is emitted statically inside the emit.hpp header file
//   meaning it is stored in the programs data segment. We can take advantage of these objects
//   residing in the same location by capturing the high order 32 bits of a typeinfo address
//   then the variant low 32 bits will be stored inside metadata
//
// (We could pack these better but this should get the job done!)
// If we are in the RC old space:
// - high [RC - 28][Allocated - 1][Young - 1][Root - 1][Marked - 1][Type Ptr Low Bits - 32]
//
// If we are in the nursery:
// - high [Forward Index - 28][Allocated - 1][Young - 1][Root - 1][Marked - 1][Type Ptr Low Bits -32]
//

#define NUM_TYPEPTR_BITS 32

#define TYPE_PTR_MASK 0x0000'0000'FFFF'FFFFUL
#define RC_MASK       0xFFFF'FFF0'0000'0000UL
#define FORWARD_MASK  0xFFFF'FFF0'0000'0000UL

#define ISALLOC_MASK  0x0000'0008'0000'0000UL
#define ISYOUNG_MASK  0x0000'0004'0000'0000UL
#define ISROOT_MASK   0x0000'0002'0000'0000UL
#define ISMARKED_MASK 0x0000'0001'0000'0000UL

#define NUM_BIT_FLAGS 4
#define RC_AND_FORWARD_SHIFT (NUM_TYPEPTR_BITS + NUM_BIT_FLAGS)

#ifdef VERBOSE_HEADER
struct MetaData 
{
    //!!!! alloc info is valid even when this is in a free-list so we need to make sure it does not collide with the free-list data !!!!
    __CoreGC::TypeInfoBase* type;
    bool isalloc;
    bool isyoung;
    bool ismarked;
    bool isroot;
    //TODO -- also a parent thread root bit (that we don't clear but we treat as a root for the purposes of marking etc.)
    int32_t forward_index;
    int32_t ref_count;
}; 
#else
typedef struct MetaData 
{
    //!!!! alloc info is valid even when this is in a free-list so we need to make sure it is a 0 bit in the pointer value (low 3) !!!!
    uint64_t meta; //8 byte bit vector
} MetaData;
static_assert(sizeof(MetaData) == 8, "MetaData size is not 8 bytes");
#endif

#define NON_FORWARDED 0

#define GC_GET_META_DATA_ADDR(O) ((MetaData*)((uint8_t*)O - sizeof(MetaData)))

#ifdef VERBOSE_HEADER
// Resets an objects metadata and updates with index into forward table
#define RESET_METADATA_FOR_OBJECT(M, FP) ((*(M)) = { .type=nullptr, .isalloc=false, .isyoung=true, .ismarked=false, .isroot=false, .forward_index=FP, .ref_count=0 })
#define ZERO_METADATA(M) ((*(M)) = {})

#define GC_IS_MARKED(O) (GC_GET_META_DATA_ADDR(O))->ismarked
#define GC_IS_YOUNG(O) (GC_GET_META_DATA_ADDR(O))->isyoung
#define GC_IS_ALLOCATED(O) (GC_GET_META_DATA_ADDR(O))->isalloc
#define GC_IS_ROOT(O) (GC_GET_META_DATA_ADDR(O))->isroot

#define GC_FWD_INDEX(O) (GC_GET_META_DATA_ADDR(O))->forward_index
#define GC_REF_COUNT(O) (GC_GET_META_DATA_ADDR(O))->ref_count

#define GC_TYPE(O) (GC_GET_META_DATA_ADDR(O))->type

#define INC_REF_COUNT(O) (++GC_REF_COUNT(O))
#define DEC_REF_COUNT(O) (--GC_REF_COUNT(O))

#define GC_RESET_ALLOC(META) { (META)->isalloc = false; }

#define GC_SHOULD_VISIT(META) ((META)->isyoung && !(META)->ismarked)

#define GC_SHOULD_PROCESS_AS_ROOT(META) ((META)->isalloc && !(META)->isroot)
#define GC_SHOULD_PROCESS_AS_YOUNG(META) ((META)->isyoung)

#define GC_MARK_AS_ROOT(META) { (META)->isroot = true; }
#define GC_MARK_AS_MARKED(META) { (META)->ismarked = true; }

#define GC_CLEAR_YOUNG_MARK(META) { (META)->isyoung = false; }
#define GC_CLEAR_ROOT_MARK(META) { (META)->ismarked = false; (META)->isroot = false; }

#define GC_SHOULD_FREE_LIST_ADD(META) (!(META)->isalloc || ((META)->isyoung && (META)->forward_index == NON_FORWARDED))

#else
// Resets an objects metadata and updates with index into forward table
#define ZERO_METADATA(M) (((M)->meta) = 0x0UL)
#define RESET_METADATA_FOR_OBJECT(M, FP) SET_FORWARD_INDEX(M, FP)

#define GC_IS_MARKED(O)    ((GC_GET_META_DATA_ADDR(O)->meta & ISMARKED_MASK) != 0UL)
#define GC_IS_YOUNG(O)     ((GC_GET_META_DATA_ADDR(O)->meta & ISYOUNG_MASK) != 0UL)
#define GC_IS_ALLOCATED(O) ((GC_GET_META_DATA_ADDR(O)->meta & ISALLOC_MASK) != 0UL)
#define GC_IS_ROOT(O)      ((GC_GET_META_DATA_ADDR(O)->meta & ISROOT_MASK) != 0UL)

#define GC_FWD_INDEX(O)    (static_cast<uint32_t>((GC_GET_META_DATA_ADDR(O)->meta & FORWARD_MASK) >> RC_AND_FORWARD_SHIFT))
#define GC_REF_COUNT(O)    (static_cast<uint32_t>((GC_GET_META_DATA_ADDR(O)->meta & RC_MASK) >> RC_AND_FORWARD_SHIFT))

#define GET_TYPE_PTR(O)    ((GC_GET_META_DATA_ADDR(O)->meta & TYPE_PTR_MASK) | (gtl_info.typeptr_high32 << NUM_TYPEPTR_BITS)) 
#define GC_TYPE(O)         (reinterpret_cast<__CoreGC::TypeInfoBase*>(GET_TYPE_PTR(O)))

#define SET_REF_COUNT(O, COUNT)     (GC_GET_META_DATA_ADDR(O)->meta = (GC_GET_META_DATA_ADDR(O)->meta & ~RC_MASK) | ((static_cast<uintptr_t>(COUNT) << RC_AND_FORWARD_SHIFT) & RC_MASK))
#define SET_FORWARD_INDEX(O, COUNT) (GC_GET_META_DATA_ADDR(O)->meta = (GC_GET_META_DATA_ADDR(O)->meta & ~FORWARD_MASK) | ((static_cast<uintptr_t>(COUNT) << RC_AND_FORWARD_SHIFT) & FORWARD_MASK))

// Sets low 32 bits of ptr in meta
#define SET_TYPE_PTR(META, PTR) ((META)->meta = ((META)->meta & ~TYPE_PTR_MASK) | (reinterpret_cast<uintptr_t>(PTR) & TYPE_PTR_MASK))

#define INC_REF_COUNT(O) (SET_REF_COUNT(O, GC_REF_COUNT(O) + 1UL))
#define DEC_REF_COUNT(O) (SET_REF_COUNT(O, GC_REF_COUNT(O) - 1UL))

#define GC_RESET_ALLOC(META)  (((META)->meta) &= ~ISALLOC_MASK) 
#define GC_SHOULD_VISIT(META) ((((META)->meta) & ISYOUNG_MASK) && !(((META)->meta) & ISMARKED_MASK))

#define GC_SHOULD_PROCESS_AS_ROOT(META)  ((((META)->meta) & ISALLOC_MASK) && !(((META)->meta) & ISROOT_MASK))
#define GC_SHOULD_PROCESS_AS_YOUNG(META) (((META)->meta) & ISYOUNG_MASK)

#define GC_MARK_AS_ROOT(META)   (((META)->meta) |= ISROOT_MASK)
#define GC_MARK_AS_MARKED(META) (((META)->meta) |= ISMARKED_MASK)

#define GC_CLEAR_YOUNG_MARK(META) (((META)->meta) &= ~ISYOUNG_MASK) 
#define GC_CLEAR_ROOT_MARK(META)  (((META)->meta) &= ~(ISROOT_MASK | ISYOUNG_MASK)) 

#define GC_SHOULD_FREE_LIST_ADD(META) ( \
    !((META)->meta & ISALLOC_MASK) || ( \
        ((META)->meta & ISYOUNG_MASK) && \
        (static_cast<uint32_t>(((META)->meta & FORWARD_MASK) >> RC_AND_FORWARD_SHIFT) == NON_FORWARDED) \
    ) \
)
#endif

#ifdef MEM_STATS
#define TOTAL_ALLOC_COUNT(E)      (E).mstats.total_alloc_count
#define TOTAL_ALLOC_MEMORY(E)     (E).mstats.total_alloc_memory
#define TOTAL_LIVE_BYTES(E)       (E).mstats.total_live_bytes
#define TOTAL_COLLECTIONS(E)      (E).mstats.total_collections
#define MIN_COLLECTION_TIME(E)    (E).mstats.min_collection_time
#define MAX_COLLECTION_TIME(E)    (E).mstats.max_collection_time
#define MAX_LIVE_HEAP(E)          (E).mstats.max_live_heap

#define UPDATE_TOTAL_ALLOC_COUNT(E, OP, ...)      TOTAL_ALLOC_COUNT((E)) OP __VA_ARGS__
#define UPDATE_TOTAL_ALLOC_MEMORY(E, OP, ...)     TOTAL_ALLOC_MEMORY((E)) OP __VA_ARGS__
#define UPDATE_TOTAL_LIVE_BYTES(E, OP, ...)       TOTAL_LIVE_BYTES((E)) OP __VA_ARGS__
#define UPDATE_TOTAL_COLLECTIONS(E, OP, ...)      TOTAL_COLLECTIONS((E)) OP __VA_ARGS__
#define UPDATE_MIN_COLLECTION_TIME(E, OP, ...)    MIN_COLLECTION_TIME((E)) OP __VA_ARGS__
#define UPDATE_MAX_COLLECTION_TIME(E, OP, ...)    MAX_COLLECTION_TIME((E)) OP __VA_ARGS__
#define UPDATE_MAX_LIVE_HEAP(E, OP, ...)          MAX_LIVE_HEAP((E)) OP __VA_ARGS__
#else 
#define TOTAL_ALLOC_COUNT(E)                      (0)
#define TOTAL_ALLOC_MEMORY(E)                     (0)
#define TOTAL_LIVE_BYTES(E)                       (0)
#define TOTAL_COLLECTIONS(E)                      (0)
#define MIN_COLLECTION_TIME(E)                    (0)
#define MAX_COLLECTION_TIME(E)                    (0)
#define MAX_LIVE_HEAP(E)                          (0)

#define UPDATE_TOTAL_ALLOC_COUNT(E, OP, ...)
#define UPDATE_TOTAL_ALLOC_MEMORY(E, OP, ...)
#define UPDATE_TOTAL_LIVE_BYTES(E, OP, ...)
#define UPDATE_TOTAL_COLLECTIONS(E, OP, ...)
#define UPDATE_MIN_COLLECTION_TIME(E, OP, ...)
#define UPDATE_MAX_COLLECTION_TIME(E, OP, ...)
#define UPDATE_MAX_LIVE_HEAP(E, OP, ...)
#endif
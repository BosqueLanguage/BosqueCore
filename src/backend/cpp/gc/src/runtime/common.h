#pragma once

#include "../language/bsqtype.h"
#include "./support/memstats.h"

#include <sys/mman.h> //mmap

//DEFAULT ENABLED WHILE LOTS OF DEVELOPMENT!!!!
// MEM_STATS defined in support/memstats.h
#define BSQ_GC_CHECK_ENABLED
#define VERBOSE_HEADER

//
// Note: If we are deterministic the base addresses for our pages
// will be outside of asan's address range. Will need to run asan
// in non-deterministic
//
#define ALLOC_DEBUG_MEM_DETERMINISTIC

#ifdef BSQ_GC_CHECK_ENABLED
#define ALLOC_DEBUG_MEM_INITIALIZE

#define ALLOC_DEBUG_CANARY
#define DSA_INVARIANTS
#define GC_INVARIANTS
#endif

#ifdef ALLOC_DEBUG_MEM_DETERMINISTIC
#define ALLOC_BASE_ADDRESS ((void*)(0x4000000000ul)) 
#define ALLOC_ADDRESS_SPAN 2147483648ul
#endif

//Make sure any allocated page is addressable by us -- larger than 2^31 and less than 2^42
#define MIN_ALLOCATED_ADDRESS ((void*)(2147483648ul))
#define MAX_ALLOCATED_ADDRESS ((void*)(281474976710656ul))

#define BSQ_MEM_ALIGNMENT 8

// If BITS_IN_ADDR_FOR_PAGE != 12 mmap fails or will not garuntee the correct size block 
// unless compiled in  non-deterministic mode (as it is not a multiple of default page size, 4kb)
#define BITS_IN_ADDR_FOR_PAGE 13ul
#define BSQ_BLOCK_ALLOCATION_SIZE (1ul << BITS_IN_ADDR_FOR_PAGE)

#define PAGE_MASK ((1ul << BITS_IN_ADDR_FOR_PAGE) - 1ul)
#define PAGE_ADDR_MASK (~PAGE_MASK)

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
#define BSQ_FULL_NURSERY_THRESHOLD static_cast<float>(BSQ_COLLECTION_THRESHOLD)

//Max number of decrement ops we do per collection -- 
//    TODO:we may need to make this a bit dynamic 
#define BSQ_INITIAL_MAX_DECREMENT_COUNT (BSQ_COLLECTION_THRESHOLD * BSQ_BLOCK_ALLOCATION_SIZE) / (BSQ_MEM_ALIGNMENT * 32)

// TODO: Arbitrary size for now
#define MAX_DECD_PAGES 10'000

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
// - When we are in the nursery the rc_fwd field will store an index into our forward table
// - When we are in the old space the rc_fwd field will store a reference count
//

#define NUM_TYPEPTR_BITS 32
#define TYPEPTR_MASK 0x0000'0000'FFFF'FFFFUL

// TODO: Temporary hack for getting approximate data seg address
//       --- used in packed metadata
static const char* GC_DATA_SEGMENT_ANCHOR = "GC_DATA_SEGMENT_BASE";
static const uint64_t g_typeptr_high32 = (reinterpret_cast<uint64_t>(&GC_DATA_SEGMENT_ANCHOR) >> NUM_TYPEPTR_BITS);

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
    union {
        uint64_t raw;
        struct {
            uint64_t typeptr_low : 32;
            uint64_t isalloc : 1;
            uint64_t isyoung : 1;
            uint64_t ismarked : 1;
            uint64_t isroot : 1;
            uint64_t rc_fwd : 28;
        } bits;
    };
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

#define GC_CHECK_BOOL_BYTES(M) \
do { \
    int8_t isalloc_byte = *reinterpret_cast<const int8_t*>(&(M)->isalloc); \
    int8_t isyoung_byte = *reinterpret_cast<const int8_t*>(&(M)->isyoung); \
    int8_t ismarked_byte = *reinterpret_cast<const int8_t*>(&(M)->ismarked); \
    int8_t isroot_byte = *reinterpret_cast<const int8_t*>(&(M)->isroot); \
    GC_INVARIANT_CHECK(isalloc_byte == 0 || isalloc_byte == 1); \
    GC_INVARIANT_CHECK(isyoung_byte == 0 || isyoung_byte == 1); \
    GC_INVARIANT_CHECK(ismarked_byte == 0 || ismarked_byte == 1); \
    GC_INVARIANT_CHECK(isroot_byte == 0 || isroot_byte == 1); \
} while(0)

#else
// Resets an objects metadata and updates with index into forward table
#define ZERO_METADATA(M) ((M)->raw = 0x0UL)
#define RESET_METADATA_FOR_OBJECT(M, FP) \
    do { \
        ZERO_METADATA(M); \
        (M)->bits.isyoung = 1; \
        (M)->bits.rc_fwd = FP; \
    } while(0); 

#define GC_IS_MARKED(O)    (GC_GET_META_DATA_ADDR(O)->bits.ismarked)
#define GC_IS_YOUNG(O)     (GC_GET_META_DATA_ADDR(O)->bits.isyoung)
#define GC_IS_ALLOCATED(O) (GC_GET_META_DATA_ADDR(O)->bits.isalloc)
#define GC_IS_ROOT(O)      (GC_GET_META_DATA_ADDR(O)->bits.isroot)

#define GC_FWD_INDEX(O)    (GC_GET_META_DATA_ADDR(O)->bits.rc_fwd)
#define GC_REF_COUNT(O)    (GC_GET_META_DATA_ADDR(O)->bits.rc_fwd)

#define GET_TYPE_PTR(O)    ((GC_GET_META_DATA_ADDR(O)->bits.typeptr_low) | (g_typeptr_high32 << NUM_TYPEPTR_BITS)) 
#define GC_TYPE(O)         (reinterpret_cast<__CoreGC::TypeInfoBase*>(GET_TYPE_PTR(O)))

// Sets low 32 bits of ptr in meta
#define SET_TYPE_PTR(META, PTR) ((META)->bits.typeptr_low = reinterpret_cast<uintptr_t>(PTR) & TYPEPTR_MASK)
        
#define INC_REF_COUNT(O) (++GC_GET_META_DATA_ADDR(O)->bits.rc_fwd)
#define DEC_REF_COUNT(O) (--GC_GET_META_DATA_ADDR(O)->bits.rc_fwd)

#define GC_RESET_ALLOC(META)  ((META)->bits.isalloc = 0) 
#define GC_SHOULD_VISIT(META) ((META)->bits.isyoung && !(META)->bits.ismarked)

#define GC_SHOULD_PROCESS_AS_ROOT(META)  ((META)->bits.isalloc && !(META)->bits.isroot)
#define GC_SHOULD_PROCESS_AS_YOUNG(META) ((META)->bits.isyoung)

#define GC_MARK_AS_ROOT(META)   ((META)->bits.isroot = 1)
#define GC_MARK_AS_MARKED(META) ((META)->bits.ismarked = 1)

#define GC_CLEAR_YOUNG_MARK(META) ((META)->bits.isyoung = 0) 
#define GC_CLEAR_ROOT_MARK(META) \
    do { \
        (META)->bits.isroot = 0; \
        (META)->bits.ismarked = 0; \
    } while(0)

#define GC_SHOULD_FREE_LIST_ADD(META) (!(META)->bits.isalloc || ((META)->bits.isyoung && (META)->bits.rc_fwd == NON_FORWARDED ))

#define GC_CHECK_BOOL_BYTES(M) \
do { \
    GC_INVARIANT_CHECK((M)->bits.isalloc == 0 || (M)->bits.isalloc == 1); \
    GC_INVARIANT_CHECK((M)->bits.isyoung == 0 || (M)->bits.isyoung == 1); \
    GC_INVARIANT_CHECK((M)->bits.ismarked == 0 || (M)->bits.ismarked == 1); \
    GC_INVARIANT_CHECK((M)->bits.isroot == 0 || (M)->bits.isroot == 1); \
} while(0)

#endif // VERBOSE_HEADER
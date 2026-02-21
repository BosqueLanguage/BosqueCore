#pragma once

#include "../language/bsqtype.h"
#include "./support/memstats.h"

#include <sys/mman.h> //mmap
#include <mutex>

/////////////////////////////////////////////////
// - Building `debug` (make BUILD=debug) enables MEM_STATS, BSQ_GC_CHECK_ENABLED
//   , and VERBOSE_HEADER (all flags, most debug output and uses -O0)
// - Building `dev` (make BUILD=dev) disables all flags and builds with -O0
// - Building `release` (make BUILD=release) disables all flags and builds 
//   with -O2
// - If finer flag control is desired compiliation, options `-DMEM_STATS`
//   , `-DBSQ_GC_CHECK_ENABLED` and `-DVERBOSE_HEADER` may be specified
//   and enabled through the cli argument `OPTIONS` 
//   (i.e. make BUILD=release OPTIONS=-DMEM_STATS)
// - The experimental `epsilon` allocator may be used for comparison of 
//   GC performance to a simple bump-pointer allocator (no gc). To enable add
//   the CLI argument `ALLOC=epsilon`

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

#ifdef BSQ_GC_TESTING
#	define NUM_THREAD_TESTING_ROOTS 16
#endif

#define MAX_THREADS 64 + 1 /*+1 for decs processor*/

#define RST  "\x1B[0m"
#define BOLD(x)	"\x1B[1m" x RST
#define UNDL(x)	"\x1B[4m" x RST

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
#define BSQ_MAX_ALLOC_SLOTS 1024ul

//Number of allocation pages we fill up before we start collecting
#define BSQ_COLLECTION_THRESHOLD 1024 
#define BSQ_FULL_NURSERY_THRESHOLD static_cast<float>(BSQ_COLLECTION_THRESHOLD)

//Max number of decrement ops we do per collection -- 
//    TODO:we may need to make this a bit dynamic 
#define BSQ_INITIAL_MAX_DECREMENT_COUNT \
	(BSQ_COLLECTION_THRESHOLD * (BSQ_BLOCK_ALLOCATION_SIZE - sizeof(PageInfo)) / (BSQ_MEM_ALIGNMENT + sizeof(MetaData)))

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

// memsrc & memtrgt are 8byte aligned ptrs and n is the number if 8byte words to copy
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
extern std::mutex g_alloclock;

//A global mutex lock that all threads will use when doing shared GC ops (e.g. getting pages or root resolution)
extern std::mutex g_gcmemlock;

//A global mutex lock that all threads will use when doing shared GC ops (e.g. when doing their inc/dec ref loops)
extern std::mutex g_gcrefctlock;

// A global mutex lock that all threads will use when merging their thread local
// memstats into the global memstats
extern std::mutex g_gctelemetrylock;

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
// - When we are in the nursery the rc_fwd field will store an index into our forward table
// - When we are in the old space the rc_fwd field will store a reference count

#ifdef VERBOSE_HEADER
struct MetaData 
{
    //!!!! alloc info is valid even when this is in a free-list so we need to make sure it does not collide with the free-list data !!!!
    bool isalloc;
    bool isyoung;
    bool ismarked;
    //TODO -- also a parent thread root bit (that we don't clear but we treat as a root for the purposes of marking etc.) 
	int32_t thd_count;
	int32_t forward_index;
    int32_t ref_count;
}; 
#else
// NOTE we may be interested in making metadata 32 bits with 21 bits for rc_fwd
struct MetaData 
{
    //!!!! alloc info is valid even when this is in a free-list so we need to make sure it is a 0 bit in the pointer value (low 3) !!!!
    union {
        struct {
            uint64_t isalloc  : 1;
            uint64_t isyoung  : 1;
            uint64_t ismarked : 1;
            uint64_t thd_count: 7;
            uint64_t rc_fwd   : 54;
        } bits;
        uint64_t raw;
    };
};
static_assert(sizeof(MetaData) == 8, "MetaData size is not 8 bytes");
#endif

#define NON_FORWARDED 0

#define GC_GET_META_DATA_ADDR(O) \
	PageInfo::getObjectMetadataAligned(O)

#define GC_TYPE(META) ((PageInfo::extractPageFromPointer(META))->typeinfo)

// TODO a lot of duplicated code here! we should only have raw field access
// behind ifdefs
#ifdef VERBOSE_HEADER
// Resets an objects metadata and updates with index into forward table
#define RESET_METADATA_FOR_OBJECT(META, FP) ((*(META)) = { .isalloc=false, .isyoung=true, .ismarked=false, .thd_count=0, .forward_index=FP, .ref_count=0 })
#define ZERO_METADATA(META) ((*(META)) = {})

#define GC_IS_MARKED(META)    ((META)->ismarked)
#define GC_IS_YOUNG(META)     ((META)->isyoung)
#define GC_IS_ALLOCATED(META) ((META)->isalloc)
#define GC_THREAD_COUNT(META) ((META)->thd_count)
#define GC_IS_ROOT(META)      (GC_THREAD_COUNT(META) > 0)

#define GC_FWD_INDEX(META) ((META)->forward_index)
#define GC_REF_COUNT(META) ((META)->ref_count)

#define INC_REF_COUNT(META) (++GC_REF_COUNT(META))
#define DEC_REF_COUNT(META) (--GC_REF_COUNT(META))

#define GC_RESET_ALLOC(META) { (META)->isalloc = false; }

#define GC_SHOULD_VISIT(META) ((META)->isyoung && !(META)->ismarked)

#define GC_SHOULD_PROCESS_AS_YOUNG(META) ((META)->isyoung)

#define GC_MARK_AS_ROOT(META) { (META)->thd_count++; }
#define GC_DROP_ROOT_REF(META) { (META)->thd_count--; }
#define GC_MARK_AS_MARKED(META) { (META)->ismarked = true; }

#define GC_CLEAR_YOUNG_MARK(META)  { GC_IS_YOUNG(META) = false; }
#define GC_CLEAR_MARKED_MARK(META) { GC_IS_MARKED(META) = false; }

#define GC_SHOULD_FREE_LIST_ADD(META) \
	(!GC_IS_ALLOCATED(META) \
		|| (GC_IS_YOUNG(META) && GC_FWD_INDEX(META) == NON_FORWARDED))

#define GC_CHECK_BOOL_BYTES(META) \
do { \
    int8_t isalloc_byte  = *reinterpret_cast<int8_t*>(&(META)->isalloc); \
    int8_t isyoung_byte  = *reinterpret_cast<int8_t*>(&(META)->isyoung); \
    int8_t ismarked_byte = *reinterpret_cast<int8_t*>(&(META)->ismarked); \
    int8_t thd_count_raw = *reinterpret_cast<int8_t*>(&(META)->thd_count); \
	GC_INVARIANT_CHECK(isalloc_byte == 0 || isalloc_byte == 1); \
    GC_INVARIANT_CHECK(isyoung_byte == 0 || isyoung_byte == 1); \
    GC_INVARIANT_CHECK(ismarked_byte == 0 || ismarked_byte == 1); \
    GC_INVARIANT_CHECK(thd_count_raw >= 0); \
} while(0)

#else
// Resets an objects metadata and updates with index into forward table
#define ZERO_METADATA(META) ((META)->raw = 0x0UL)
#define RESET_METADATA_FOR_OBJECT(META, FP) \
do { \
	ZERO_METADATA(META); \
	(META)->bits.isyoung = 1; \
	(META)->bits.rc_fwd = FP; \
} while(0); 

#define GC_IS_MARKED(META)    ((META)->bits.ismarked)
#define GC_IS_YOUNG(META)     ((META)->bits.isyoung)
#define GC_IS_ALLOCATED(META) ((META)->bits.isalloc)
#define GC_THREAD_COUNT(META) ((META)->bits.thd_count)
#define GC_IS_ROOT(META)      (GC_THREAD_COUNT(META) > 0)

#define GC_FWD_INDEX(META)    ((META)->bits.rc_fwd)
#define GC_REF_COUNT(META)    ((META)->bits.rc_fwd)

#define INC_REF_COUNT(META) (++GC_REF_COUNT(META))
#define DEC_REF_COUNT(META) (--GC_REF_COUNT(META))

#define GC_RESET_ALLOC(META)  ((META)->bits.isalloc = 0) 
#define GC_SHOULD_VISIT(META) (GC_IS_YOUNG(META) && !GC_IS_MARKED(META))

#define GC_SHOULD_PROCESS_AS_YOUNG(META) (GC_IS_YOUNG(META))

#define GC_MARK_AS_ROOT(META)   { (META)->bits.thd_count++; }
#define GC_DROP_ROOT_REF(META)  { (META)->bits.thd_count--; }
#define GC_MARK_AS_MARKED(META) { (META)->bits.ismarked = 1; }

#define GC_CLEAR_YOUNG_MARK(META)  { GC_IS_YOUNG(META) = 0; }
#define GC_CLEAR_MARKED_MARK(META) { GC_IS_MARKED(META) = 0; }

#define GC_SHOULD_FREE_LIST_ADD(META) \
	(!GC_IS_ALLOCATED(META) \
		|| (GC_IS_YOUNG(META) && GC_FWD_INDEX(META) == NON_FORWARDED))

#define GC_CHECK_BOOL_BYTES(META)

#endif // VERBOSE_HEADER

#define METADATA_DUMP(META) \
	std::cout << "Meta Data at " << META << ":" << std::endl \
	<< "\tisalloc: " << GC_IS_ALLOCATED(META) << std::endl \
	<< "\tisyoung: " << GC_IS_YOUNG(META) << std::endl \
	<< "\tismarked: " << GC_IS_MARKED(META) << std::endl \
	<< "\tthread count: " << GC_THREAD_COUNT(META) << std::endl \
	<< "\tref count: " << GC_REF_COUNT(META) << std::endl \
	<< "\tforward index: " << GC_FWD_INDEX(META) << std::endl;

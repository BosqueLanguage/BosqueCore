#pragma once

#include <cmath>
#include <cstring>
#include <csetjmp>

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#include <optional>
#include <chrono>
#include <random>
#include <string>
#include <map>
#include <list>
#include <stack>
#include <algorithm>

#include <type_traits>
#include <concepts>

#include <mutex>
#include <thread>

//Only for internal diagnostics
#include <assert.h>

namespace ᐸRuntimeᐳ
{
    constexpr int64_t BSQ_NUMERIC_DYNAMIC_RANGE_BASE = 4611686018427387903ll;
    constexpr __int128_t BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED = ((__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE * (__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE);

    enum class ErrorKind
    {
        Generic,
        OutOfMemory,
        RuntimeAssertion,

        NumericBounds,
        NumericUnderflow,
        DivisionByZero,

        InvalidCast,

        UserAbort,
        UserAssertion,
        UserInvariant,
        UserValidation,
        UserPrecondition,
        UserPostcondition
    };

    class ErrorInfo
    {
    public:
        const char* file;
        uint32_t line;

        ErrorKind kerror;
        const char* tag; //optional
        const char* message; //optional
    };

    template <typename U> 
    concept ConceptUnionRepr = std::is_union<U>::value;

    //slow path error handler
    [[noreturn]] void bsq_handle_error(const char* file, uint32_t line, ErrorKind kerror, const char* tag, const char* message);

    [[noreturn]] inline void bsq_abort(const char* file, uint32_t line, const char* tag, const char* message)
    {
        bsq_handle_error(file, line, ErrorKind::UserAbort, tag, message);
    }

    inline void bsq_assert(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserAssertion, tag, message);
        }
    }

    inline void bsq_validate(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserValidation, tag, message);
        }
    }

    inline void bsq_invariant(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserInvariant, tag, message);
        }
    }

    inline void bsq_requires(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserPrecondition, tag, message);
        }
    }

    inline void bsq_ensures(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserPostcondition, tag, message);
        }
    }

    //forward declaration of types that are stored in a thread local way
    class TaskInfo;

    class BosqueThreadLocalInfo
    {
    public:
        TaskInfo* current_task;

        BosqueThreadLocalInfo() : current_task(nullptr) {}

        // Cannot copy or move thread local info
        BosqueThreadLocalInfo(const BosqueThreadLocalInfo&) = delete;
        BosqueThreadLocalInfo &operator=(const BosqueThreadLocalInfo&) = delete;

        static void generate_uuid4(char out[16])
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }

        static void generate_uuid7(char out[16])
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }
    };


    extern thread_local BosqueThreadLocalInfo tl_bosque_info;

    //See also allocator/alloc.h for allocator specific thread local and global info -- no other globals should be hanging around!
}

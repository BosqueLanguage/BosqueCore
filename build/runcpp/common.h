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
#include <algorithm>

#include <type_traits>
#include <concepts>

#include <threads.h>

//Only for internal diagnostics
#include <assert.h>

namespace ᐸRuntimeᐳ
{
    constexpr int64_t BSQ_NUMERIC_DYNAMIC_RANGE_BASE = 4611686018427387903ll;
    constexpr __int128_t BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED = ((__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE * (__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE);

    constexpr int32_t buildlevel_release = 0;
    constexpr int32_t buildlevel_test = 1;
    constexpr int32_t buildlevel_debug = 2;

#ifndef BSQ_BUILD_LEVEL
    constexpr int32_t current_build_level = buildlevel_debug;
#else
    constexpr int32_t current_build_level = BSQ_BUILD_LEVEL;
#endif

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

    template<int32_t enabled>
    inline void runtime_assert_specialized(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {   
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::RuntimeAssertion, tag, message);
        }
    }

    template<>
    inline void runtime_assert_specialized<0>(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {   
        ;
    }

    template<int32_t level>
    inline void runtime_assert(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {   
        static_assert(level >= buildlevel_release && level <= buildlevel_debug, "Invalid build level for runtime_assert");
        runtime_assert_specialized<level == current_build_level>(cond, file, line, tag, message);
    }

    inline void bsq_assert(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserAssertion, tag, message);
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

    class ThreadLocalInfo
    {
    public:
        TaskInfo* current_task;

        ThreadLocalInfo() noexcept : current_task(nullptr) {}

        // Cannot copy or move thread local info
        ThreadLocalInfo(const ThreadLocalInfo&) = delete;
        ThreadLocalInfo &operator=(const ThreadLocalInfo&) = delete;

        static void generate_uuid4(char out[16]) noexcept
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }

        static void generate_uuid7(char out[16]) noexcept
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }
    };


    extern thread_local ThreadLocalInfo tl_info;
}

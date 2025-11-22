#pragma once

#include <cmath>
#include <cstring>
#include <csetjmp>

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#include <optional>
#include <array>
#include <string>
#include <map>
#include <list>
#include <type_traits>

#include <threads.h>

//Only for internal diagnostics
#include <assert.h>

#define BSQ_NUMERIC_DYNAMIC_RANGE_BASE 4611686018427387903ull
#define BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED ((__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE * (__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE)

namespace Core
{
    using None = uint64_t;
    using Bool = uint64_t;

    namespace ᐸRuntimeᐳ
    {
        constexpr None none = 0ull;
        constexpr Bool btrue = 1ull;
        constexpr Bool bfalse = 0ull;

        enum class ErrorKind
        {
            Generic,
            OutOfMemory,

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

        //slow path error handler
        [[noreturn]] void bsq_handle_error(const char* file, uint32_t line, ErrorKind kerror, const char* tag, const char* message);

        [[noreturn]] inline void bsq_abort(const char* file, uint32_t line, const char* tag, const char* message)
        {
            bsq_handle_error(file, line, ErrorKind::UserAbort, tag, message);
        }

        inline void bsq_assert(Bool cond, const char* file, uint32_t line, const char* tag, const char* message)
        {
            if(!cond) [[unlikely]] {
                bsq_handle_error(file, line, ErrorKind::UserAssertion, tag, message);
            }
        }

        inline void bsq_invariant(Bool cond, const char* file, uint32_t line, const char* tag, const char* message)
        {
            if(!cond) [[unlikely]] {
                bsq_handle_error(file, line, ErrorKind::UserInvariant, tag, message);
            }
        }

        inline void bsq_requires(Bool cond, const char* file, uint32_t line, const char* tag, const char* message)
        {
            if(!cond) [[unlikely]] {
                bsq_handle_error(file, line, ErrorKind::UserPrecondition, tag, message);
            }
        }

        inline void bsq_ensures(Bool cond, const char* file, uint32_t line, const char* tag, const char* message)
        {
            if(!cond) [[unlikely]] {
                bsq_handle_error(file, line, ErrorKind::UserPostcondition, tag, message);
            }
        }

        class ThreadLocalInfo
        {
        public:
            std::list<std::jmp_buf> error_handler;
            std::optional<ErrorInfo> pending_error;

            ThreadLocalInfo() {}

            // Cannot copy or move thread local info
            ThreadLocalInfo(const ThreadLocalInfo&) = delete;
            ThreadLocalInfo &operator=(const ThreadLocalInfo&) = delete;
        };


        extern thread_local ThreadLocalInfo tl_info;
    }
}

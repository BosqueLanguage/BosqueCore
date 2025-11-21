#pragma once

#include <cmath>
#include <csetjmp>

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#include <optional>
#include <string>
#include <map>
#include <list>

#include <threads.h>

//Only for internal diagnostics
#include <assert.h>

#define BSQ_HANDLE_ERROR(FILE, LINE, KERR, TAG, MSG) ᐸRuntimeᐳ::tl_info.pending_error = { FILE, LINE, KERR, TAG, MSG }; std::longjmp(ᐸRuntimeᐳ::tl_info.error_handler.back(), 11);

#define BSQ_ABORT(E, FILE, LINE, TAG, MSG) if(!(E)) { BSQ_HANDLE_ERROR(FILE, LINE, ᐸRuntimeᐳ::ErrorKind::UserAbort, TAG, MSG) }
#define BSQ_ASSERT(E, FILE, LINE, TAG, MSG) if(!(E)) { BSQ_HANDLE_ERROR(FILE, LINE, ᐸRuntimeᐳ::ErrorKind::UserAssertion, TAG, MSG) }

#define BSQ_INVARIANT(E, FILE, LINE, TAG, MSG) if(!(E)) { BSQ_HANDLE_ERROR(FILE, LINE, ᐸRuntimeᐳ::ErrorKind::UserInvariant, TAG, MSG) }
#define BSQ_REQUIRES(E, FILE, LINE, TAG, MSG) if(!(E)) { BSQ_HANDLE_ERROR(FILE, LINE, ᐸRuntimeᐳ::ErrorKind::UserPrecondition, TAG, MSG) }
#define BSQ_ENSURES(E, FILE, LINE, TAG, MSG) if(!(E)) { BSQ_HANDLE_ERROR(FILE, LINE, ᐸRuntimeᐳ::ErrorKind::UserPostcondition, TAG, MSG) }

#define none 0ull
#define btrue 1ull
#define bfalse 0ull

#define BSQ_NUMERIC_DYNAMIC_RANGE_BASE 4611686018427387903ull
#define BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED ((__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE * (__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE)

namespace Core
{
    namespace ᐸRuntimeᐳ
    {
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

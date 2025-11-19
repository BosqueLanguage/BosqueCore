#pragma once

#include <cmath>
#include <csetjmp>

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#include <list>

#include <threads.h>

//Only for internal diagnostics
#include <assert.h>

#define BSQ_ABORT (std::longjmp(Core::Runtime::tl_info.error_handler.back(), 11))
#define BSQ_ASSERT(E) if(!(E)) { BSQ_ABORT; }
#define BSQ_REQUIRES(E) BSQ_ASSERT(E)
#define BSQ_ENSURES(E) BSQ_ASSERT(E)

#define none 0ull
#define btrue 1ull
#define bfalse 0ull

namespace Core
{
    namespace Runtime
    {
        class ThreadLocalInfo
        {
        public:
            std::list<std::jmp_buf> error_handler;

            ThreadLocalInfo() {}

            // Cannot copy or move thread local info
            ThreadLocalInfo(const ThreadLocalInfo&) = delete;
            ThreadLocalInfo &operator=(const ThreadLocalInfo&) = delete;
        };


        thread_local ThreadLocalInfo& tl_info;
    }
}

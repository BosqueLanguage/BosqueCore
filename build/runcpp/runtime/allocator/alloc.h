#pragma once

#include <stdint.h>
#include <stddef.h>

namespace ᐸRuntimeᐳ
{
    constexpr size_t BSQ_BUFFER_ALLOCATOR_BLOCK_SIZE = 4096;

    //
    //TODO: need a shared allocator implementation for i/o buffers that we can link in the server and here for BSQON processing
    //
}


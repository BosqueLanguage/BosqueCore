#pragma once

#include <stdint.h>
#include <stddef.h>

namespace ᐸRuntimeᐳ
{
    constexpr size_t BSQ_BUFFER_ALLOCATOR_BLOCK_SIZE = 4096;

    //IO Buffer type of size BSQ_BUFFER_ALLOCATOR_BLOCK_SIZE
    using BSQIOBuffer = uint8_t*;

    //
    //TODO: need a shared allocator implementation for i/o buffers that we can link in the server and here for BSQON processing
    //
}


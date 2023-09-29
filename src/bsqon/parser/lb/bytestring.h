#pragma once

#include <stdint.h>

struct ByteString
{
    uint8_t* bytes;
    uint64_t len;
};

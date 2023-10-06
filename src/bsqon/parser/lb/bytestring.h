#pragma once

#include <stdint.h>
#include <stdbool.h>

#define AST_ALLOC_ALIGN_8(size) (((size) + 7) & ~7)
#define AST_ALLOC(size) malloc(AST_ALLOC_ALIGN_8(size))
#define AST_FREE(ptr) free(ptr)

struct ByteString
{
    uint8_t* bytes;
    uint64_t len;
};

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

#define AST_ALLOC_ALIGN_8(size) (((size) + 7) & ~7)
#define AST_ALLOC(size) malloc(AST_ALLOC_ALIGN_8(size))

#define AST_STRDUP(str) strdup(str)

struct ByteString
{
    uint8_t* bytes;
    uint64_t len;
};

struct ByteString* bstrAlloc(struct ByteString dst);
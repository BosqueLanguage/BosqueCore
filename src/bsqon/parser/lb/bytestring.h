#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
extern "C" 
{
#endif

#define AST_ALLOC_ALIGN_8(size) (((size) + 7) & ~7)
#define AST_ALLOC(size) malloc(AST_ALLOC_ALIGN_8(size))

#define AST_STRDUP(str) strdup(str)

struct ByteString
{
    uint8_t* bytes;
    uint64_t len;
};

struct ByteString* bstrAlloc(struct ByteString dst);

struct AST_SourcePos
{
    uint32_t first_line;
    uint32_t first_column;
    uint32_t last_line;
    uint32_t last_column;
};

struct AST_SourcePos createSourcePos(uint32_t first_line, uint32_t first_column, uint32_t last_line, uint32_t last_column);

#ifdef __cplusplus
}
#endif

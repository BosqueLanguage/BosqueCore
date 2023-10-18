#include "./bytestring.h"

struct ByteString* bstrAlloc(struct ByteString dst)
{
    struct ByteString* res = (struct ByteString*)malloc(sizeof(struct ByteString) + dst.len + 1);
    memset((char*)res, 0, sizeof(struct ByteString) + dst.len + 1);

    res->bytes = (uint8_t*)res + sizeof(struct ByteString);
    memcpy(res->bytes, dst.bytes, dst.len);
    res->len = dst.len;

    return res;
}

struct SourcePos createSourcePos(uint32_t first_line, uint32_t first_column, uint32_t last_line, uint32_t last_column)
{
    struct SourcePos res;
    res.first_line = first_line;
    res.first_column = first_column;
    res.last_line = last_line;
    res.last_column = last_column;
    return res;
}

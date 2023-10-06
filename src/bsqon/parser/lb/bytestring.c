#include "./bytestring.h"

void buff_clear(char* src, size_t len)
{
    memset(src, 0, len);
}

void chars_copy(struct ByteString* dst, const char* src, size_t len)
{
    memcpy(dst->bytes, src, len);
    dst->len = len;
}

void bytes_copy(struct ByteString* dst, struct ByteString* src)
{
    memcpy(dst->bytes, src->bytes, src->len);
    dst->len = src->len;
}

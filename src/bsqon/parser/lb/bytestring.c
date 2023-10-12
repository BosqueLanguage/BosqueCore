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

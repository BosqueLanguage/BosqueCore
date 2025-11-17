#pragma once

#include "common.h"

#define PTR_MASK_NOP ('0')
#define PTR_MASK_PTR ('1')
#define PTR_MASK_TAGGED ('2')

#define PTR_MASK_LEAF nullptr

namespace __CoreGC {

enum Tag 
{
    Value,
    Ref,
    Tagged
};

struct FieldOffsetInfo 
{
    uint16_t id;
    uint16_t type;
    uint32_t byteoffset;
};

struct TypeInfoBase 
{
    uint32_t type_id;
    uint32_t type_size;
    uint32_t slot_size;
    Tag tag;
    const char* ptr_mask; //NULL is for leaf values or structs
    const char* typekey;
    const FieldOffsetInfo* vtable;
};

} // namespace __CoreGC
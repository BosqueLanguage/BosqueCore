#pragma once

#include "common.h"

#define PTR_MASK_NOP ('0')
#define PTR_MASK_PTR ('1')
#define PTR_MASK_STRING ('2')

#define LEAF_PTR_MASK nullptr

//
// TODO: Change string mask to tagged mask and
//

//An inline string has the length in the low 3 bits of the pointer
#define PTR_MASK_STRING_AND_SLOT_PTR_VALUED(M, V) ((M == PTR_MASK_STRING) & (((uintptr_t)(V) & 0x7)== 0))

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
    FieldOffsetInfo* vtable;
};

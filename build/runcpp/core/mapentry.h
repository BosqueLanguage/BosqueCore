#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    template<typename K, typename V>
    class XMapEntry
    {
    public:
        K key;
        V value;

        XMapEntry() = default;
        XMapEntry(const K &k, const V &v) : key{k}, value{v} {}
    };

    template<typename K, typename V>
    consteval TypeInfo g_typeinfo_MapEntry_generate(uint32_t id, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(XMapEntry<K, V>),
            byteSizeToSlotCount(sizeof(XMapEntry<K, V>)),
            LayoutTag::Value,
            mask,
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            name,
            false
        };
    }
}

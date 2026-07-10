#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    template<typename K, typename V>
    class MapEntry
    {
    public:
        K key;
        V value;

        MapEntry() = default;
        MapEntry(const K &k, const V &v) : key{k}, value{v} {}
    };

    template<typename K, typename V>
    consteval TypeInfo g_typeinfo_MapEntry_generate(uint32_t id, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(MapEntry<K, V>),
            byteSizeToSlotCount(sizeof(MapEntry<K, V>)),
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

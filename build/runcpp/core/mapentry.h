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
    void jsonParseToBSQ_MapEntry(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array() && j.size() == 2, "JSON -> BSQ", 0, nullptr, "Expected JSON array of size 2 for MapEntry<K, V>");

        K k;
        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        kinfo->opdispatch.jsonParseToBSQFp(kinfo, j[0], &k);

        V v;
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        vinfo->opdispatch.jsonParseToBSQFp(vinfo, j[1], &v);

        *(XMapEntry<K, V>*)resptr = XMapEntry<K, V>{k, v};
    }

    template<typename K, typename V>
    void parseToBSQ_MapEntry(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected type for MapEntry");
        lexer->consume();
        bsq_validate(lexer->testIsSymbol('{'), "BAPI -> BSQ", 0, nullptr, "Expected '{' for MapEntry");
        lexer->consume();

        K k;
        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        kinfo->opdispatch.parseToBSQFp(kinfo, lexer, &k);

        bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' in MapEntry");
        lexer->consume();

        V v;
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        vinfo->opdispatch.parseToBSQFp(vinfo, lexer, &v);

        bsq_validate(lexer->testIsSymbol('}'), "BAPI -> BSQ", 0, nullptr, "Expected '}' after MapEntry value");
        lexer->consume();

        *(XMapEntry<K, V>*)resptr = XMapEntry<K, V>{k, v};
    }

    template<typename K, typename V>
    json bsqToJSON_MapEntry(const TypeInfo* tinfo, const void* valptr)
    {
        const XMapEntry<K, V>* entry = (const XMapEntry<K, V>*)valptr;

        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        json jk = kinfo->opdispatch.bsqToJSONFp(kinfo, &entry->key);

        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        json jv = vinfo->opdispatch.bsqToJSONFp(vinfo, &entry->value);

        return json::array({jk, jv});
    }

    template<typename K, typename V>
    void bsqToBAPI_MapEntry(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const XMapEntry<K, V>* entry = (const XMapEntry<K, V>*)valptr;

        builder->appendConstString(tinfo->typekey);
        builder->appendLiteralString("{ ");

        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        kinfo->opdispatch.bsqToBAPIFp(kinfo, &entry->key, builder);

        builder->appendLiteralString(", ");

        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        vinfo->opdispatch.bsqToBAPIFp(vinfo, &entry->value, builder);
        builder->appendLiteralString(" }");
    }

    template<typename K, typename V>
    void displayValue_MapEntry(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const XMapEntry<K, V>* entry = (const XMapEntry<K, V>*)valptr;

        os << getDisplayIndent(indent) << tinfo->typekey << " { ";

        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        kinfo->opdispatch.displayFp(kinfo, &entry->key, os, indent);

        os << ", ";
        
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        vinfo->opdispatch.displayFp(vinfo, &entry->value, os, indent);

        os << " }";
    }

    template<typename K, typename V>
    consteval TypeInfo g_typeinfo_MapEntry_generate(uint32_t id, const TypeLayoutInfo* layout, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(XMapEntry<K, V>),
            byteSizeToSlotCount(sizeof(XMapEntry<K, V>)),
            LayoutTag::Value,
            mask,
            nullptr,
            0,
            layout,
            2,
            nullptr,
            0,
            TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_MapEntry<K, V>, (ParseToBSQFp)&parseToBSQ_MapEntry<K, V>, (BSQToJSONFp)&bsqToJSON_MapEntry<K, V>, (BSQToBAPIFp)&bsqToBAPI_MapEntry<K, V>, (DisplayValueFp)&displayValue_MapEntry<K, V> },
            name,
            false
        };
    }
}

#pragma once

#include "../common.h"
#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    using XNone = uint64_t;
    constexpr XNone xnone = 0ull;

    void jsonParseToBSQ_None(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_None(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_None(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_None(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_None(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_None = {
        WELL_KNOWN_TYPE_ID_NONE,
        8,
        byteSizeToSlotCount(8),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_None, (ParseToBSQFp)&parseToBSQ_None, (BSQToJSONFp)&bsqToJSON_None, (BSQToBAPIFp)&bsqToBAPI_None, (DisplayValueFp)&displayValue_None },
        "None",
        true
    };
}

#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bool.h"

namespace ᐸRuntimeᐳ
{
    class XUUIDv4
    {
    public:
        std::array<uint8_t, 16> value;

        static XUUIDv4 nil() { return XUUIDv4{}; }

        friend XBool operator==(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend XBool operator<(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend XBool operator>(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
        friend XBool operator!=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()))); }
        friend XBool operator<=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()))); }
        friend XBool operator>=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()))); }
    };

    class XUUIDv7
    {
    public:
        std::array<uint8_t, 16> value;

        static XUUIDv7 nil() { return XUUIDv7{}; }

        friend XBool operator==(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend XBool operator<(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend XBool operator>(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
        friend XBool operator!=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()))); }
        friend XBool operator<=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()))); }
        friend XBool operator>=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()))); }
    };

    void jsonParseToBSQ_UUIDv4(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_UUIDv4(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_UUIDv4(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_UUIDv4(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_UUIDv4(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_UUIDv4 = {
        WELL_KNOWN_TYPE_ID_UUIDV4,
        sizeof(XUUIDv4),
        byteSizeToSlotCount(sizeof(XUUIDv4)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_UUIDv4, (ParseToBSQFp)&parseToBSQ_UUIDv4, (BSQToJSONFp)&bsqToJSON_UUIDv4, (BSQToBAPIFp)&bsqToBAPI_UUIDv4, (DisplayValueFp)&displayValue_UUIDv4 },
        "UUIDv4",
        true
    };

    void jsonParseToBSQ_UUIDv7(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_UUIDv7(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_UUIDv7(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_UUIDv7(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_UUIDv7(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_UUIDv7 = {
        WELL_KNOWN_TYPE_ID_UUIDV7,
        sizeof(XUUIDv7),
        byteSizeToSlotCount(sizeof(XUUIDv7)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_UUIDv7, (ParseToBSQFp)&parseToBSQ_UUIDv7, (BSQToJSONFp)&bsqToJSON_UUIDv7, (BSQToBAPIFp)&bsqToBAPI_UUIDv7, (DisplayValueFp)&displayValue_UUIDv7 },
        "UUIDv7",
        true
    };
}

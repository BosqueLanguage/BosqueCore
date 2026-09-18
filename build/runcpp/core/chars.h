#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bool.h"

namespace ᐸRuntimeᐳ 
{
    class XByte
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend XBool operator==(const XByte &lhs, const XByte &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XByte &lhs, const XByte &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XByte &lhs, const XByte &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XCChar
    {
    public:
        int64_t value; // Stored as int64_t for alignment reasons

        friend XBool operator==(const XCChar &lhs, const XCChar &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XCChar &lhs, const XCChar &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XCChar &lhs, const XCChar &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XUnicodeChar
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons
        
        friend XBool operator==(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    void jsonParseToBSQ_Byte(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_Byte(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_Byte(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_Byte(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_Byte(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_Byte = {
        WELL_KNOWN_TYPE_ID_BYTE,
        sizeof(XByte),
        byteSizeToSlotCount(sizeof(XByte)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_Byte, (ParseToBSQFp)&parseToBSQ_Byte, (BSQToJSONFp)&bsqToJSON_Byte, (BSQToBAPIFp)&bsqToBAPI_Byte, (DisplayValueFp)&displayValue_Byte },
        "Byte",
        true
    };

    void jsonParseToBSQ_CChar(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_CChar(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_CChar(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_CChar(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_CChar(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_CChar = {
        WELL_KNOWN_TYPE_ID_CCHAR,
        sizeof(XCChar),
        byteSizeToSlotCount(sizeof(XCChar)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_CChar, (ParseToBSQFp)&parseToBSQ_CChar, (BSQToJSONFp)&bsqToJSON_CChar, (BSQToBAPIFp)&bsqToBAPI_CChar, (DisplayValueFp)&displayValue_CChar },
        "CChar",
        true
    };

    void jsonParseToBSQ_UnicodeChar(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_UnicodeChar(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_UnicodeChar(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_UnicodeChar(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_UnicodeChar(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_UnicodeChar = {
        WELL_KNOWN_TYPE_ID_UNICODECHAR,
        sizeof(XUnicodeChar),
        byteSizeToSlotCount(sizeof(XUnicodeChar)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_UnicodeChar, (ParseToBSQFp)&parseToBSQ_UnicodeChar, (BSQToJSONFp)&bsqToJSON_UnicodeChar, (BSQToBAPIFp)&bsqToBAPI_UnicodeChar, (DisplayValueFp)&displayValue_UnicodeChar },
        "UnicodeChar",
        true
    };
}

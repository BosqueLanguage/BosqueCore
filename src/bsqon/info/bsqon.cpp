#include "bsqon.h"

namespace BSQON
{
    UnicodeString StringValue::unescapeString(const uint8_t* bytes, size_t length)
    {
        xxxx;
    }

    std::vector<uint8_t> StringValue::escapeString(UnicodeString sv)
    {
        xxxx;
    }

    StringValue* StringValue::createFromParse(const Type* vtype, const uint8_t* bytes, size_t length)
    {
        return new StringValue(vtype, StringValue::unescapeString(bytes, length));
    }

    std::string ASCIIStringValue::unescapeString(const char* chars, size_t length)
    {
        xxxx;
    }

    std::vector<uint8_t> ASCIIStringValue::escapeString(std::string sv)
    {
        xxxx;
    }

    ASCIIStringValue* ASCIIStringValue::createFromParse(const Type* vtype, const char* bytes, size_t length)
    {
        return new ASCIIStringValue(vtype, ASCIIStringValue::unescapeString(bytes, length));
    }

    StringOfValue* StringOfValue::createFromParse(const Type* vtype, const uint8_t* bytes, size_t length, const BSQRegex* validator)
    {
        UnicodeString str = std::move(StringValue::unescapeString(bytes, length));
        return validator->test(&str) ? new StringOfValue(vtype, std::move(str)) : nullptr;
    }

    ASCIIStringOfValue* createFromParse(const Type* vtype, const char* chars, size_t length, const BSQRegex* validator)
    {
        xxxx;
    }
}


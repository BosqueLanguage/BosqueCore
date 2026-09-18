#include "bool.h"

namespace ᐸRuntimeᐳ
{
    void validatingConstructor_Bool(void** argptr, void* resptr)
    {
        *(XBool*)resptr = *(XBool*)(*argptr);
    }

    void jsonParseToBSQ_Bool(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_boolean(), "JSON -> BSQ", 0, nullptr, "Expected boolean for Bool type");
        *(XBool*)resptr = j.get<bool>() ? XTRUE : XFALSE;
    }

    void parseToBSQ_Bool(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsTrue() || lexer->testIsFalse(), "BAPI -> BSQ", 0, nullptr, "Expected 'true' or 'false' literal for Bool type");
        *(XBool*)resptr = lexer->testIsTrue() ? XTRUE : XFALSE;
        lexer->consume();
    }

    json bsqToJSON_Bool(const TypeInfo* tinfo, const void* valptr)
    {
        return json((bool)(*(XBool*)valptr == XTRUE));
    }

    void bsqToBAPI_Bool(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        builder->appendConstString((bool)(*(XBool*)valptr == XTRUE) ? "true" : "false");
    }

    void displayValue_Bool(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        os << getDisplayIndent(indent) << ((bool)(*(XBool*)valptr == XTRUE) ? "true" : "false");
    }
}

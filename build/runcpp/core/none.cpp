#include "none.h"

namespace ᐸRuntimeᐳ
{
    void jsonParseToBSQ_None(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_null(), "JSON -> BSQ", 0, nullptr, "Expected null for None type");
        *(uint64_t*)resptr = xnone;
    }

    void parseToBSQ_None(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsNone(), "BAPI -> BSQ", 0, nullptr, "Expected 'none' literal for None type");
        *(uint64_t*)resptr = xnone;
        lexer->consume();
    }

    json bsqToJSON_None(const TypeInfo* tinfo, const void* valptr)
    {
        return json(nullptr);
    }

    void bsqToBAPI_None(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        builder->appendConstString("none");
    }

    void displayValue_None(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        os << getDisplayIndent(indent) << "none";
    }
}

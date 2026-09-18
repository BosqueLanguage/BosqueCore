#include "fpoints.h"

namespace ᐸRuntimeᐳ 
{
    size_t writeFloatNumber(XFloat val, std::array<char, 64>& numbuf)
    {
        return std::snprintf(numbuf.data(), numbuf.size(), "%03.12lff", val.value);
    }

    void jsonParseToBSQ_Float(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_number(), "JSON -> BSQ", 0, nullptr, "Expected JSON number for Float type");

        double vv = j.get<double>();
        bsq_validate(XFloat::isValidFloat(vv), "JSON -> BSQ", 0, nullptr, "Invalid JSON encoding for Float type");
        *(XFloat*)resptr = XFloat{vv};
    }

    void parseToBSQ_Float(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralFloat, "BAPI -> BSQ", 0, nullptr, "Expected literal Float token");

        double vv = 0;
        bool isok = lexer->tryExtractNumericValue<double>(vv);

        bsq_validate(isok && XFloat::isValidFloat(vv), "BAPI -> BSQ", 0, nullptr, "Invalid literal Float token");
        *(XFloat*)resptr = XFloat{vv};
        lexer->consume();
    }

    json bsqToJSON_Float(const TypeInfo* tinfo, const void* valptr)
    {
        XFloat n = *(XFloat*)valptr;
        return json(n.value);
    }

    void bsqToBAPI_Float(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        XFloat n = *(XFloat*)valptr;
        std::array<char, 64> numbuf;
        size_t written = writeFloatNumber(n, numbuf);

        builder->appendConstString(numbuf.data(), written);
    }

    void displayValue_Float(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        XFloat n = *(XFloat*)valptr;
        std::array<char, 64> numbuf;
        size_t written = writeFloatNumber(n, numbuf);

        os << getDisplayIndent(indent) << std::string(numbuf.data(), written);
    }
}

#include "integrals.h"

namespace ᐸRuntimeᐳ
{
    constexpr int64_t JSON_MIN_SAFE_INTEGER = -9007199254740991; // -(2^53 - 1)
    constexpr int64_t JSON_MAX_SAFE_INTEGER = 9007199254740991; // 2^53 - 1

    size_t writeNatNumber(XNat val, std::array<char, 64>& numbuf, bool addsuffix)
    {
        if(addsuffix) {
            return std::snprintf(numbuf.data(), numbuf.size(), "%llin", (long long int)val.value);
        }
        else {
            return std::snprintf(numbuf.data(), numbuf.size(), "%lli", (long long int)val.value);
        }
    }

    size_t writeIntNumber(XInt val, std::array<char, 64>& numbuf, bool addsuffix)
    {
        if(addsuffix) {
            return std::snprintf(numbuf.data(), numbuf.size(), "%llii", (long long int)val.value);
        }
        else {
            return std::snprintf(numbuf.data(), numbuf.size(), "%lli", (long long int)val.value);
        }
    }

    size_t writeChkNatNumberSafe(XChkNat val, std::array<char, 64>& numbuf, bool addsuffix)
    {
        std::string ll = std::format("{}", val.value);
        if(addsuffix) {
            return std::snprintf(numbuf.data(), numbuf.size(), "%sN", ll.c_str());
        }
        else {
            return std::snprintf(numbuf.data(), numbuf.size(), "%s", ll.c_str());
        }
    }

    size_t writeChkIntNumberSafe(XChkInt val, std::array<char, 64>& numbuf, bool addsuffix)
    {
        std::string ll = std::format("{}", val.value);
        if(addsuffix) {
            return std::snprintf(numbuf.data(), numbuf.size(), "%sI", ll.c_str());
        }
        else {
            return std::snprintf(numbuf.data(), numbuf.size(), "%s", ll.c_str());
        }
    }

    ///////////////////////////////
    //Nat
    ///////////////////////////////

    void jsonParseToBSQ_Nat(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        if(j.is_number_unsigned()) {
            bsq_validate(XNat::isValidNat(j.get<int64_t>()), "JSON -> BSQ", 0, nullptr, "Invalid string encoding for Nat type");
            *(XNat*)resptr = XNat{ j.get<int64_t>() };
        }
        else {
            bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected unsigned number (or string encoding) for Nat type");
            
            int64_t vv = 0;
            std::string nstr = j.get<std::string>();
            auto [_, ec] = std::from_chars(skipPlusSignOpt(nstr.data()), nstr.data() + nstr.size(), vv);

            bsq_validate(ec == std::errc() && XNat::isValidNat(vv), "JSON -> BSQ", 0, nullptr, "Invalid string encoding for Nat type");
            *(XNat*)resptr = XNat{vv};
        }
    }

    void parseToBSQ_Nat(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralNat, "BAPI -> BSQ", 0, nullptr, "Expected literal Nat token");

        int64_t vv = 0;
        bool isok = lexer->tryExtractNumericValue<int64_t>(vv);

        bsq_validate(isok && XNat::isValidNat(vv), "BAPI -> BSQ", 0, nullptr, "Invalid literal Nat token");
        *(XNat*)resptr = XNat{vv};
        lexer->consume();
    }

    json bsqToJSON_Nat(const TypeInfo* tinfo, const void* valptr)
    {
        XNat n = *(XNat*)valptr;
        if(n.value <= JSON_MAX_SAFE_INTEGER) {
            return json(n.value);
        }
        else {
            std::array<char, 64> numbuf;
            size_t written = writeNatNumber(n, numbuf, false);

            return json(std::string(numbuf.data(), written));
        }
    }

    void bsqToBAPI_Nat(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        XNat n = *(XNat*)valptr;
        std::array<char, 64> numbuf;
        size_t written = writeNatNumber(n, numbuf, true);

        builder->appendConstString(numbuf.data(), written);
    }

    void displayValue_Nat(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        XNat n = *(XNat*)valptr;
        std::array<char, 64> numbuf;
        size_t written = writeNatNumber(n, numbuf, true);
        
        os << getDisplayIndent(indent) << std::string(numbuf.data(), written);
    }

    ///////////////////////////////
    //Int
    ///////////////////////////////

    void jsonParseToBSQ_Int(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        if(j.is_number_integer()) {
            bsq_validate(XInt::isValidInt(j.get<int64_t>()), "JSON -> BSQ", 0, nullptr, "Invalid JSON encoding for Int type");
            *(XInt*)resptr = XInt{ j.get<int64_t>() };
        }
        else {
            bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected number (or string encoding) for Int type");
            
            int64_t vv = 0;
            std::string nstr = j.get<std::string>();
            auto [_, ec] = std::from_chars(skipPlusSignOpt(nstr.data()), nstr.data() + nstr.size(), vv);

            bsq_validate(ec == std::errc(), "JSON -> BSQ", 0, nullptr, "Invalid string encoding for Int type");
            *(XInt*)resptr = XInt{vv};
        }
    }

    void parseToBSQ_Int(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralInt, "BAPI -> BSQ", 0, nullptr, "Expected literal Int token");

        int64_t vv = 0;
        bool isok = lexer->tryExtractNumericValue<int64_t>(vv);

        bsq_validate(isok && XInt::isValidInt(vv), "BAPI -> BSQ", 0, nullptr, "Invalid literal Int token");
        *(XInt*)resptr = XInt{vv};
        lexer->consume();
    }

    json bsqToJSON_Int(const TypeInfo* tinfo, const void* valptr)
    {
        XInt n = *(XInt*)valptr;
        if(JSON_MIN_SAFE_INTEGER <= n.value && n.value <= JSON_MAX_SAFE_INTEGER) {
            return json(n.value);
        }
        else {
            std::array<char, 64> numbuf;
            size_t written = writeIntNumber(n, numbuf, false);

            return json(std::string(numbuf.data(), written));
        }
    }

    void bsqToBAPI_Int(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        XInt n = *(XInt*)valptr;
        std::array<char, 64> numbuf;
        size_t written = writeIntNumber(n, numbuf, true);

        builder->appendConstString(numbuf.data(), written);
    }

    void displayValue_Int(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        XInt n = *(XInt*)valptr;
        std::array<char, 64> numbuf;
        size_t written = writeIntNumber(n, numbuf, true);
        
        os << getDisplayIndent(indent) << std::string(numbuf.data(), written);
    }

    ///////////////////////////////
    //ChkNat
    ///////////////////////////////

    void jsonParseToBSQ_ChkNat(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        if(j.is_number_unsigned()) {
            bsq_validate(XChkNat::isValidNat(j.get<int64_t>()), "JSON -> BSQ", 0, nullptr, "Invalid JSON encoding for ChkNat type");
            *(XChkNat*)resptr = XChkNat{ j.get<int64_t>() };
        }
        else {
            bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected number (or string encoding) for ChkNat type");

            std::string strval = j.get<std::string>();
            if(strval == "ChkNat::npos") {
                *(XChkNat*)resptr = XChkNat::bliteral();
            }
            else {
                __int128_t vv = 0;
                std::string nstr = j.get<std::string>();
                auto [_, ec] = std::from_chars(skipPlusSignOpt(nstr.data()), nstr.data() + nstr.size(), vv);

                bsq_validate(ec == std::errc() && XChkNat::isValidNat(vv), "JSON -> BSQ", 0, nullptr, "Invalid string encoding for ChkNat type");
                *(XChkNat*)resptr = XChkNat{ vv };
            }
        }
    }

    void parseToBSQ_ChkNat(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralChkNat, "BAPI -> BSQ", 0, nullptr, "Expected literal ChkNat token");
        bsq_validate(lexer->getCurrentTokenDataSize() < 64, "BAPI -> BSQ", 0, nullptr, "Expected literal ChkNat token");

        constexpr const char* nposStr = "ChkNat::npos";

        std::array<uint8_t, 64> outbuff;
        size_t ssize = lexer->extractSmallToken(outbuff);

        if(std::strcmp(reinterpret_cast<const char*>(outbuff.data()), nposStr) == 0) {
            *(XChkNat*)resptr = XChkNat::bliteral();
        }
        else {
            __int128_t vv = 0;
            bool isok = lexer->tryExtractNumericValue<__int128_t>(vv);

            bsq_validate(isok && XChkNat::isValidNat(vv), "BAPI -> BSQ", 0, nullptr, "Invalid literal ChkNat token");
            *(XChkNat*)resptr = XChkNat{vv};
        }
        lexer->consume();
    }

    json bsqToJSON_ChkNat(const TypeInfo* tinfo, const void* valptr)
    {
        XChkNat n = *(XChkNat*)valptr;
        if(JSON_MIN_SAFE_INTEGER <= n.value && n.value <= JSON_MAX_SAFE_INTEGER) {
            return json(n.value);
        }
        else {
            if(n.isBottom()) {
                return json("ChkNat::npos");
            }
            else {
                std::array<char, 64> numbuf;
                size_t written = writeChkNatNumberSafe(n, numbuf, false);

                return json(std::string(numbuf.data(), written));
            }
        }
    }

    void bsqToBAPI_ChkNat(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        XChkNat n = *(XChkNat*)valptr;
        if(n.isBottom()) {
            builder->appendConstString("ChkNat::npos");
        }
        else {
            std::array<char, 64> numbuf;
            size_t written = writeChkNatNumberSafe(n, numbuf, true);

            builder->appendConstString(numbuf.data(), written);
        }
    }

    void displayValue_ChkNat(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        XChkNat n = *(XChkNat*)valptr;
        if(n.isBottom()) {
            os << getDisplayIndent(indent) << "ChkNat::npos";
        }
        else {
            std::array<char, 64> numbuf;
            size_t written = writeChkNatNumberSafe(n, numbuf, true);

            os << getDisplayIndent(indent) << std::string(numbuf.data(), written);
        }
    }

    ///////////////////////////////
    //ChkInt
    ///////////////////////////////

    void jsonParseToBSQ_ChkInt(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        if(j.is_number_integer()) {
            bsq_validate(XChkInt::isValidInt(j.get<int64_t>()), "JSON -> BSQ", 0, nullptr, "Invalid JSON encoding for ChkInt type");
            *(XChkInt*)resptr = XChkInt{ j.get<int64_t>() };
        }
        else {
            bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected number (or string encoding) for ChkInt type");

            std::string strval = j.get<std::string>();
            if(strval == "ChkInt::npos") {
                *(XChkInt*)resptr = XChkInt::bliteral();
            }
            else {
                __int128_t vv = 0;
                std::string nstr = j.get<std::string>();
                auto [_, ec] = std::from_chars(skipPlusSignOpt(nstr.data()), nstr.data() + nstr.size(), vv);

                bsq_validate(ec == std::errc() && XChkInt::isValidInt(vv), "JSON -> BSQ", 0, nullptr, "Invalid string encoding for ChkInt type");
                *(XChkInt*)resptr = XChkInt{ vv };
            }
        }
    }

    void parseToBSQ_ChkInt(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralChkInt, "BAPI -> BSQ", 0, nullptr, "Expected literal ChkInt token");
        bsq_validate(lexer->getCurrentTokenDataSize() < 64, "BAPI -> BSQ", 0, nullptr, "Expected literal ChkInt token");
        
        constexpr const char* nposStr = "ChkInt::npos";

        std::array<uint8_t, 64> outbuff;
        size_t ssize = lexer->extractSmallToken(outbuff);

        if(std::strcmp(reinterpret_cast<const char*>(outbuff.data()), nposStr) == 0) {
            *(XChkInt*)resptr = XChkInt::bliteral();
        }
        else {
            __int128_t vv = 0;
            bool isok = lexer->tryExtractNumericValue<__int128_t>(vv);

            bsq_validate(isok && XChkInt::isValidInt(vv), "BAPI -> BSQ", 0, nullptr, "Invalid literal ChkInt token");
            *(XChkInt*)resptr = XChkInt{vv};
        }
        lexer->consume();
    }

    json bsqToJSON_ChkInt(const TypeInfo* tinfo, const void* valptr)
    {
        XChkInt n = *(XChkInt*)valptr;
        if(JSON_MIN_SAFE_INTEGER <= n.value && n.value <= JSON_MAX_SAFE_INTEGER) {
            return json(n.value);
        }
        else {
            if(n.isBottom()) {
                return json("ChkInt::npos");
            }
            else {
                std::array<char, 64> numbuf;
                size_t written = writeChkIntNumberSafe(n, numbuf, false);

                return json(std::string(numbuf.data(), written));
            }
        }
    }

    void bsqToBAPI_ChkInt(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        XChkInt n = *(XChkInt*)valptr;
        if(n.isBottom()) {
            builder->appendConstString("ChkInt::npos");
        }
        else {
            std::array<char, 64> numbuf;
            size_t written = writeChkIntNumberSafe(n, numbuf, true);

            builder->appendConstString(numbuf.data(), written);
        }
    }

    void displayValue_ChkInt(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        XChkInt n = *(XChkInt*)valptr;
        if(n.isBottom()) {
            os << getDisplayIndent(indent) << "ChkInt::npos";
        }
        else {
            std::array<char, 64> numbuf;
            size_t written = writeChkIntNumberSafe(n, numbuf, true);

            os << getDisplayIndent(indent) << std::string(numbuf.data(), written);
        }
    }
}

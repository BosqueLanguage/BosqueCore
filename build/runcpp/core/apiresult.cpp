#include "apiresult.h"

namespace ᐸRuntimeᐳ
{
    std::optional<XAPIInfoTag> convertStringToXAPIInfoTag(const char* str)
    {
        if(strcmp(str, "APIInfoTag::Clear") == 0) {
            return std::make_optional(XAPIInfoTag::Clear);
        }
        else if(strcmp(str, "APIInfoTag::Timeout") == 0) {
            return std::make_optional(XAPIInfoTag::Timeout);
        }
        else if(strcmp(str, "APIInfoTag::Cancelled") == 0) {
            return std::make_optional(XAPIInfoTag::Cancelled);
        }
        else if(strcmp(str, "APIInfoTag::AccessDenied") == 0) {
            return std::make_optional(XAPIInfoTag::AccessDenied);
        }
        else if(strcmp(str, "APIInfoTag::Error") == 0) {
            return std::make_optional(XAPIInfoTag::Error);
        }
        else {
            return std::nullopt;
        }
    }

    const char* convertXAPIInfoTagToString(XAPIInfoTag tag)
    {
        switch(tag)
        {
            case XAPIInfoTag::Clear: {
                return "APIInfoTag::Clear";
            }
            case XAPIInfoTag::Timeout: {
                return "APIInfoTag::Timeout";
            }
            case XAPIInfoTag::Cancelled: {
                return "APIInfoTag::Cancelled";
            }
            case XAPIInfoTag::AccessDenied: {
                return "APIInfoTag::AccessDenied";
            }
            case XAPIInfoTag::Error: {
                return "APIInfoTag::Error";
            }
            default: {
                assert(false); // Unknown XAPIInfoTag
            }
        }
    }

    XAPIResultData jsonParseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, const json& j)
    {
        bsq_validate(j.is_object(), "JSON -> BSQ", 0, nullptr, "Expected an object for APIResultEntityInfo");
        
        XAPIInfoTag tagid = XAPIInfoTag::Clear;
        if(j.contains("tagid")) {
            bsq_validate(j["tagid"].is_string(), "JSON -> BSQ", 0, nullptr, "Expected a string for tagid");
            std::string tagidstr = j["tagid"].get<std::string>();
            auto optTag = convertStringToXAPIInfoTag(tagidstr.c_str());
            bsq_validate(optTag.has_value(), "JSON -> BSQ", 0, nullptr, "Invalid tagid value");
            tagid = optTag.value();
        }

        XUUIDv4 infoid = XUUIDv4::nil();
        if(j.contains("infoid")) {
            jsonParseToBSQ_UUIDv4(tinfo, j["infoid"], &infoid);
        }

        const char* tag = nullptr;
        if(j.contains("tag")) {
            assert(false); //We need to intern or lookup these tags somehow
        }

        return XAPIResultData{tagid, infoid, tag};
    }

    XAPIResultData parseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, BAPILexer* lexer)
    {
        if(lexer->testIsSymbol('}')) {
            return XAPIResultData{XAPIInfoTag::Clear, XUUIDv4::nil(), nullptr};
        }
        else {
            bsq_validate(lexer->testIsSymbol(','), "Parse -> BSQ", 0, nullptr, "Expected ','");
            lexer->consume();
           
            bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralString && lexer->getCurrentTokenDataSize() < 64, "Parse -> BSQ", 0, nullptr, "Expected a string for tagid");
            std::array<uint8_t, 64> outchars{};
            lexer->extractSmallToken(outchars);
            auto optTag = convertStringToXAPIInfoTag(reinterpret_cast<const char*>(outchars.data()));
            bsq_validate(optTag.has_value(), "Parse -> BSQ", 0, nullptr, "Invalid tagid value");
            XAPIInfoTag tagid = optTag.value();
            
            XUUIDv4 infoid = XUUIDv4::nil();
            parseToBSQ_UUIDv4(tinfo, lexer, &infoid);

            const char* tag = nullptr;
            if(lexer->testIsSymbol(',')) {
                lexer->consume();
                assert(false); //We need to intern or lookup these tags somehow
            }

            return XAPIResultData{tagid, infoid, tag};
        }
    }

    void bsqToJSON_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, json& j)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
            j["tagid"] = std::string(convertXAPIInfoTagToString(data.tagid));
            j["infoid"] = bsqToJSON_UUIDv4(tinfo, &data.infoid);

            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }

    void bsqToBAPI_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, BSQStreamingBuilder* builder)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
            builder->appendLiteralString(", ");
            builder->appendConstString(convertXAPIInfoTagToString(data.tagid));

            bsqToBAPI_UUIDv4(tinfo, &data.infoid, builder);

            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }

    void displayValue_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, std::ostream& os, std::optional<std::string> indent)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
            os << bsqToJSON_UUIDv4(tinfo, &data.infoid) << ", ";
            XNat tagidval{static_cast<int64_t>(data.tagid)};
            os << bsqToJSON_Nat(tinfo, &tagidval);
            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }
}

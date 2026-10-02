#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "integrals.h"
#include "uuids.h"
#include "boxed.h"

namespace ᐸRuntimeᐳ
{
    enum class XAPIInfoTag : uint64_t
    {
        Clear = 0,
        Timeout = 1,
        Cancelled = 2,
        AccessDenied = 3,
        Error = 4
    };

    class XAPIResultData
    {
    public:
        XUUIDv7 correlationid;
        XUUIDv4 infoid;

        XAPIInfoTag tagid;
        const char* tag; //Type::id format to correlate ad-hoc
    };
    static_assert(sizeof(XAPIResultData) == 48, "Need to update values in compiler");

    enum class XAPIResultKind : uint64_t
    {
        Error,
        Rejected,
        Denied,
        Dropped,
        Success
    };

    template <typename T>
    class XAPIResultEntityValue
    {
    public:
        XAPIResultData data;
        T value;
    };

    template <typename T, XAPIResultKind K>
    class XAPIResultEntityValueWTag : public XAPIResultEntityValue<T>
    {
    public:
        XAPIResultEntityValueWTag() = default;
        XAPIResultEntityValueWTag(const XAPIResultEntityValueWTag& other) = default;
        XAPIResultEntityValueWTag(const XAPIResultData& data, const T& value) : XAPIResultEntityValue<T>{data, value} {}
    };

    XAPIResultData jsonParseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, const json& j);
    XAPIResultData parseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, BAPILexer* lexer);
    void bsqToJSON_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, json& j);
    void bsqToBAPI_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, BSQStreamingBuilder* builder);
    void displayValue_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, std::ostream& os, std::optional<std::string> indent);
    
    template<typename T>
    void jsonParseToBSQ_APIResultEntity(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_object(), "BAPI -> BSQ", 0, nullptr, "Expected JSON object for entity");
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        T val;
        ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j["value"], &val);
        XAPIResultKind kind = static_cast<XAPIResultKind>(j["kind"].get<uint64_t>());
        XAPIResultData resdata = jsonParseToBSQ_APIResultEntityInfo(tinfo, j);

        *(XAPIResultEntityValue<T>*)resptr = XAPIResultEntityValue<T>{resdata, kind, val};
    }

    template<typename T>
    void parseToBSQ_APIResultEntity(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected type for entity");
        lexer->consume();
        bsq_validate(lexer->testIsSymbol('{'), "BAPI -> BSQ", 0, nullptr, "Expected { for entity");
        lexer->consume();

        T valdata;
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo->opdispatch.parseToBSQFp(ofinfo, lexer, &valdata);

        bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ','");
        lexer->consume();
        XNat kval;
        parseToBSQ_Nat(tinfo, lexer, &kval);

        XAPIResultKind kind = static_cast<XAPIResultKind>(kval.value);

        XAPIResultData resdata = XAPIResultData{}; // Initialize to default in case of failure
        if(kind != XAPIResultKind::Success) {
            lexer->consume(); //should be a ,
            resdata = parseToBSQ_APIResultEntityInfo(tinfo, lexer);
        }

        *(XAPIResultEntityValue<T>*)resptr = XAPIResultEntityValue<T>{resdata, kind, valdata};
    }
    
    template<typename T>
    json bsqToJSON_APIResultEntity(const TypeInfo* tinfo, const void* valptr)
    {

        json j = json::object();

        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        j["value"] = ofinfo->opdispatch.bsqToJSONFp(ofinfo, valptr);
        j["kind"] = static_cast<uint64_t>(static_cast<const XAPIResultEntityValue<T>*>(valptr)->kind);
        bsqToJSON_APIResultEntityInfo(tinfo, static_cast<const XAPIResultEntityValue<T>*>(valptr)->data);

        return j;
    }

    template<typename T>
    void bsqToBAPI_APIResultEntity(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const XAPIResultEntityValue<T>* val = static_cast<const XAPIResultEntityValue<T>*>(valptr);

        builder->appendConstString(tinfo->typekey);
        builder->appendLiteralString("{ ");
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo->opdispatch.bsqToBAPIFp(ofinfo, &val->value, builder);

        builder->appendLiteralString(", ");
        XNat kval{static_cast<int64_t>(val->kind)};
        bsqToBAPI_Nat(tinfo, &kval, builder);

        if(val->kind != XAPIResultKind::Success) {
            builder->appendLiteralString(", ");
            bsqToBAPI_APIResultEntityInfo(tinfo, val->data, builder);
        }

        builder->appendLiteralString(" }");
    }

    template<typename T>
    void displayValue_APIResultEntity(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const XAPIResultEntityValue<T>* val = static_cast<const XAPIResultEntityValue<T>*>(valptr);

        os << getDisplayIndent(indent) << tinfo->typekey;
        os << "{ ";
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo->opdispatch.displayFp(ofinfo, &val->value, os, indent);

        os << ", ";
        XNat kval{static_cast<int64_t>(val->kind)};
        displayValue_Nat(tinfo, &kval, os, indent);

        if(val->kind != XAPIResultKind::Success) {
            os << ", ";
            displayValue_APIResultEntityInfo(tinfo, val->data, os, indent);
        }

        os << " }";
    }

    template<ConceptUnionRepr U>
    void jsonParseToBSQ_APIResultConcept(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array() && j.size() == 2, "JSON -> BSQ", 0, nullptr, "Expected JSON envelope for APIResult");
        bsq_validate(j[0].is_string(), "JSON -> BSQ", 0, nullptr, "Expected typename as key in envelope for APIResult");

        std::string tstr = j[0].get<std::string>();
        std::optional<const TypeInfo*> ofinfo_opt = TypeInfo::tryGetTypeInfoForKey(tstr);
        bsq_validate(ofinfo_opt.has_value(), "JSON -> BSQ", 0, nullptr, "Expected valid type for APIResult");

        const TypeInfo* ofinfo = ofinfo_opt.value();
        bsq_validate(ofinfo->supertypes != nullptr && std::find(ofinfo->supertypes, ofinfo->supertypes + ofinfo->supertypescount, tinfo->bsqtypeid) != ofinfo->supertypes + ofinfo->supertypescount, "JSON -> BSQ", 0, nullptr, "Expected supertype for APIResult");
        
        U val{};
        ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j[1], &val);
        
        *(BoxedUnion<U>*)resptr = BoxedUnion<U>(ofinfo, val);
    }

    template<ConceptUnionRepr U>
    void parseToBSQ_APIResultConcept(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::Identifier, "JSON -> BSQ", 0, nullptr, "Expected identifier token for APIResult");

        std::string tstr = lexer->getTokenIdentifierAsString();
        std::optional<const TypeInfo*> ofinfo_opt = TypeInfo::tryGetTypeInfoForKey(tstr);
        bsq_validate(ofinfo_opt.has_value(), "JSON -> BSQ", 0, nullptr, "Expected valid type for APIResult");

        const TypeInfo* ofinfo = ofinfo_opt.value();
        bsq_validate(ofinfo->supertypes != nullptr && std::find(ofinfo->supertypes, ofinfo->supertypes + ofinfo->supertypescount, tinfo->bsqtypeid) != ofinfo->supertypes + ofinfo->supertypescount, "JSON -> BSQ", 0, nullptr, "Expected supertype for APIResult");
        
        U val{};
        ofinfo->opdispatch.parseToBSQFp(ofinfo, lexer, &val);
        *(BoxedUnion<U>*)resptr = BoxedUnion<U>(ofinfo, val);
    }

    template<ConceptUnionRepr U>
    json bsqToJSON_APIResultConcept(const TypeInfo* tinfo, const void* valptr)
    {
        BoxedUnion<U> u = *(const BoxedUnion<U>*)valptr;

        json j = u.typeinfo->opdispatch.bsqToJSONFp(u.typeinfo, &u.data);
        return json::array({ u.typeinfo->typekey, j });
    }

    template<ConceptUnionRepr U>
    void bsqToBAPI_APIResultConcept(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        BoxedUnion<U> u = *(const BoxedUnion<U>*)valptr;
        u.typeinfo->opdispatch.bsqToBAPIFp(u.typeinfo, &u.data, builder);
    }

    template<ConceptUnionRepr U>
    void displayValue_APIResultConcept(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        BoxedUnion<U> u = *(const BoxedUnion<U>*)valptr;
        u.typeinfo->opdispatch.displayFp(u.typeinfo, &u.data, os, indent);
    }
}

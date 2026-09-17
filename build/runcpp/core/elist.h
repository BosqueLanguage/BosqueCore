#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ 
{
    ////////////////////////////////
    //Standard processing functions for EList<2> types
    ////////////////////////////////

    template<typename T1, typename T2>
    class EList2
    {
    public:
        T1 first;
        T2 second;

        template<size_t idx, typename T>
        T at() const
        {
            static_assert(idx < 2, "Index out of bounds for EList2");
            if constexpr (idx == 0) {
                return this->first;
            }
            else {
                return this->second;
            }
        }
    };

    template<typename T1, typename T2>
    void jsonParseToBSQ_EList2(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array() && j.size() == 2, "JSON -> BSQ", 0, nullptr, "Expected JSON array for EList of 2 elements");

        T1 val1;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo1->opdispatch.jsonParseToBSQFp(ofinfo1, j[0], &val1);

        T2 val2;
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        ofinfo2->opdispatch.jsonParseToBSQFp(ofinfo2, j[1], &val2);

        *(EList2<T1, T2>*)resptr = EList2<T1, T2>{val1, val2};
    }

    template<typename T1, typename T2>
    void parseToBSQ_EList2(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsSymbol("(|"), "BAPI -> BSQ", 0, nullptr, "Expected type for EList2");
        lexer->consume();

        T1 val1;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo1->opdispatch.parseToBSQFp(ofinfo1, lexer, &val1);

        bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' between elements for EList2");
        lexer->consume();

        T2 val2;
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        ofinfo2->opdispatch.parseToBSQFp(ofinfo2, lexer, &val2);

        *(EList2<T1, T2>*)resptr = EList2<T1, T2>{val1, val2};

        bsq_validate(lexer->testIsSymbol("|)"), "BAPI -> BSQ", 0, nullptr, "Expected type for EList2");
        lexer->consume();
    }

    template<typename T1, typename T2>
    json bsqToJSON_EList2(const TypeInfo* tinfo, const void* valptr)
    {
        const EList2<T1, T2>* elist = (const EList2<T1, T2>*)valptr;

        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        json j1 = ofinfo1->opdispatch.bsqToJSONFp(ofinfo1, &elist->first);
        json j2 = ofinfo2->opdispatch.bsqToJSONFp(ofinfo2, &elist->second);

        return json::array({j1, j2});
    }

    template<typename T1, typename T2>
    void bsqToBAPI_EList2(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const EList2<T1, T2>* elist = (const EList2<T1, T2>*)valptr;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        builder->appendLiteralString("(| ");
        ofinfo1->opdispatch.bsqToBAPIFp(ofinfo1, &elist->first, builder);
        builder->appendLiteralString(", ");
        ofinfo2->opdispatch.bsqToBAPIFp(ofinfo2, &elist->second, builder);
        builder->appendLiteralString(" |)");
    }
    
    template<typename T1, typename T2>
    void displayValue_EList2(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const EList2<T1, T2>* elist = (const EList2<T1, T2>*)valptr;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        os << getDisplayIndent(indent) << tinfo->typekey << "(| ";
        ofinfo1->opdispatch.displayFp(ofinfo1, &elist->first, os, indent);
        os << ", ";
        ofinfo2->opdispatch.displayFp(ofinfo2, &elist->second, os, indent);
        os << " |)";
    }

    template<typename T1, typename T2>
    consteval TypeInfo g_typeinfo_EList2_generate(uint32_t id, const TypeLayoutInfo* layout, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(EList2<T1, T2>),
            byteSizeToSlotCount(sizeof(EList2<T1, T2>)),
            LayoutTag::Value,
            mask,
            nullptr,
            0,
            layout,
            2,
            nullptr,
            0,
            TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_EList2<T1, T2>, (ParseToBSQFp)&parseToBSQ_EList2<T1, T2>, (BSQToJSONFp)&bsqToJSON_EList2<T1, T2>, (BSQToBAPIFp)&bsqToBAPI_EList2<T1, T2>, (DisplayValueFp)&displayValue_EList2<T1, T2> },
            name,
            false
        };
    }

    ////////////////////////////////
    //Standard processing functions for EList<3> types
    ////////////////////////////////

    template<typename T1, typename T2, typename T3>
    class EList3
    {
    public:
        T1 first;
        T2 second;
        T3 third;

        template<size_t idx, typename T>
        T at() const
        {
            static_assert(idx < 3, "Index out of bounds for EList3");
            if constexpr (idx == 0) {
                return this->first;
            }
            else if constexpr (idx == 1) {
                return this->second;
            }
            else {
                return this->third;
            }
        }
    };

    template<typename T1, typename T2, typename T3>
    void jsonParseToBSQ_EList3(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array() && j.size() == 3, "JSON -> BSQ", 0, nullptr, "Expected JSON array for EList of 3 elements");

        T1 val1;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo1->opdispatch.jsonParseToBSQFp(ofinfo1, j[0], &val1);

        T2 val2;
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        ofinfo2->opdispatch.jsonParseToBSQFp(ofinfo2, j[1], &val2);

        T3 val3;
        const TypeInfo* ofinfo3 = TypeInfo::getTypeInfoForID(tinfo->ftable[2].fieldbsqtypeid);
        ofinfo3->opdispatch.jsonParseToBSQFp(ofinfo3, j[2], &val3);

        *(EList3<T1, T2, T3>*)resptr = EList3<T1, T2, T3>{val1, val2, val3};
    }

    template<typename T1, typename T2, typename T3>
    void parseToBSQ_EList3(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsSymbol("(|"), "BAPI -> BSQ", 0, nullptr, "Expected type for EList3");
        lexer->consume();

        T1 val1;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo1->opdispatch.parseToBSQFp(ofinfo1, lexer, &val1);

        bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' between elements for EList3");
        lexer->consume();

        T2 val2;
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        ofinfo2->opdispatch.parseToBSQFp(ofinfo2, lexer, &val2);

        bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' between elements for EList3");
        lexer->consume();

        T3 val3;
        const TypeInfo* ofinfo3 = TypeInfo::getTypeInfoForID(tinfo->ftable[2].fieldbsqtypeid);
        ofinfo3->opdispatch.parseToBSQFp(ofinfo3, lexer, &val3);

        *(EList3<T1, T2, T3>*)resptr = EList3<T1, T2, T3>{val1, val2, val3};

        bsq_validate(lexer->testIsSymbol("|)"), "BAPI -> BSQ", 0, nullptr, "Expected type for EList3");
        lexer->consume();
    }

    template<typename T1, typename T2, typename T3>
    json bsqToJSON_EList3(const TypeInfo* tinfo, const void* valptr)
    {
        const EList3<T1, T2, T3>* elist = (const EList3<T1, T2, T3>*)valptr;

        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        const TypeInfo* ofinfo3 = TypeInfo::getTypeInfoForID(tinfo->ftable[2].fieldbsqtypeid);

        json j1 = ofinfo1->opdispatch.bsqToJSONFp(ofinfo1, &elist->first);
        json j2 = ofinfo2->opdispatch.bsqToJSONFp(ofinfo2, &elist->second);
        json j3 = ofinfo3->opdispatch.bsqToJSONFp(ofinfo3, &elist->third);

        return json::array({j1, j2, j3});
    }

    template<typename T1, typename T2, typename T3>
    void bsqToBAPI_EList3(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const EList3<T1, T2, T3>* elist = (const EList3<T1, T2, T3>*)valptr;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        const TypeInfo* ofinfo3 = TypeInfo::getTypeInfoForID(tinfo->ftable[2].fieldbsqtypeid);

        builder->appendLiteralString("(| ");
        ofinfo1->opdispatch.bsqToBAPIFp(ofinfo1, &elist->first, builder);
        builder->appendLiteralString(", ");
        ofinfo2->opdispatch.bsqToBAPIFp(ofinfo2, &elist->second, builder);
        builder->appendLiteralString(", ");
        ofinfo3->opdispatch.bsqToBAPIFp(ofinfo3, &elist->third, builder);
        builder->appendLiteralString(" |)");
    }
    
    template<typename T1, typename T2, typename T3>
    void displayValue_EList3(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const EList3<T1, T2, T3>* elist = (const EList3<T1, T2, T3>*)valptr;
        const TypeInfo* ofinfo1 = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* ofinfo2 = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);
        const TypeInfo* ofinfo3 = TypeInfo::getTypeInfoForID(tinfo->ftable[2].fieldbsqtypeid);

        os << getDisplayIndent(indent) << tinfo->typekey << "(| ";
        ofinfo1->opdispatch.displayFp(ofinfo1, &elist->first, os, indent);
        os << ", ";
        ofinfo2->opdispatch.displayFp(ofinfo2, &elist->second, os, indent);
        os << ", ";
        ofinfo3->opdispatch.displayFp(ofinfo3, &elist->third, os, indent);
        os << " |)";
    }

    template<typename T1, typename T2, typename T3>
    consteval TypeInfo g_typeinfo_EList3_generate(uint32_t id, const TypeLayoutInfo* layout, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(EList3<T1, T2, T3>),
            byteSizeToSlotCount(sizeof(EList3<T1, T2, T3>)),
            LayoutTag::Value,
            mask,
            nullptr,
            0,
            layout,
            3,
            nullptr,
            0,
            TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_EList3<T1, T2, T3>, (ParseToBSQFp)&parseToBSQ_EList3<T1, T2, T3>, (BSQToJSONFp)&bsqToJSON_EList3<T1, T2, T3>, (BSQToBAPIFp)&bsqToBAPI_EList3<T1, T2, T3>, (DisplayValueFp)&displayValue_EList3<T1, T2, T3> },
            name,
            false
        };
    }

    ////////////////////////////////
    //Standard processing functions for EList<4> types
    ////////////////////////////////

    template<typename T1, typename T2, typename T3, typename T4>
    class EList4
    {
    public:
        T1 first;
        T2 second;
        T3 third;
        T4 fourth;

        template<size_t idx, typename T>
        T at() const
        {
            static_assert(idx < 4, "Index out of bounds for EList4");

            if constexpr (idx == 0) {
                return this->first;
            }
            else if constexpr (idx == 1) {
                return this->second;
            }
            else if constexpr (idx == 2) {
                return this->third;
            }
            else {
                return this->fourth;
            }
        }
    };
}

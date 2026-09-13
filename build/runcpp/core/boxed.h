#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "none.h"
#include "bool.h"

namespace ᐸRuntimeᐳ
{
    inline XBool isSubtypeOf(const TypeInfo* etype, const TypeInfo* oftype)
    {
        auto ii = std::find(etype->supertypes, etype->supertypes + etype->supertypescount, oftype->bsqtypeid);
        return XBool::from(ii != (etype->supertypes + etype->supertypescount));
    }

    inline XBool isNotSubtypeOf(const TypeInfo* etype, const TypeInfo* oftype)
    {
        auto ii = std::find(etype->supertypes, etype->supertypes + etype->supertypescount, oftype->bsqtypeid);
        return XBool::from(ii == (etype->supertypes + etype->supertypescount));
    }

    template <typename T>
    class XSome 
    {
    public:
        T value;
        
        friend XBool operator==(const XSome<T>& lhs, const T& rhs) { return lhs.value == rhs; }
        friend XBool operator==(const T& lhs, const XSome<T>& rhs) { return lhs == rhs.value; }
        friend XBool operator!=(const XSome<T>& lhs, const T& rhs) { return lhs.value != rhs; }
        friend XBool operator!=(const T& lhs, const XSome<T>& rhs) { return lhs != rhs.value; }
    };

    template<typename T>
    void jsonParseToBSQ_Some(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array() && j.size() == 2, "JSON -> BSQ", 0, nullptr, "Expected JSON envelope for some<T>");
        bsq_validate(j[0] == "some" || j[0] == tinfo->typekey, "JSON -> BSQ", 0, nullptr, "Expected 'some' keyword or full type in JSON envelope for some<T>");

        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        T val;
        ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j[1], &val);

        *(XSome<T>*)resptr = XSome<T>{val};
    }

    template<typename T>
    void parseToBSQ_Some(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bool isisome = lexer->testIsKeyword("some");
        bsq_validate(lexer->testIsKeyword("some") || lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected 'some' keyword or full type for some<T>");
        lexer->consume();

        bsq_validate((isisome && lexer->testIsSymbol('(')) || (!isisome && lexer->testIsSymbol('{')), "BAPI -> BSQ", 0, nullptr, "Missing open paren (or wrong paren) in some<T>");
        lexer->consume();

        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        T val;
        ofinfo->opdispatch.parseToBSQFp(ofinfo, lexer, &val);

        bsq_validate((isisome && lexer->testIsSymbol(')')) || (!isisome && lexer->testIsSymbol('}')), "BAPI -> BSQ", 0, nullptr, "Missing close paren (or wrong paren) in some<T>");
        lexer->consume();

        *(XSome<T>*)resptr = XSome<T>{val};
    }

    template<typename T>
    json bsqToJSON_Some(const TypeInfo* tinfo, const void* valptr)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const XSome<T>* some = (const XSome<T>*)valptr;
        
        return json::array({ "some", ofinfo->opdispatch.bsqToJSONFp(ofinfo, &some->value) });
    }

    template<typename T>
    void bsqToBAPI_Some(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        //void BSQ_emit${ctname}(const ${ctname}& vv) { ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("some"); ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol('('); BSQ_emit${voptttname}(vv.value); ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol(')'); }
        
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const XSome<T>* some = (const XSome<T>*)valptr;
        
        builder->appendLiteralString("some");
        builder->appendChar('(');
        ofinfo->opdispatch.bsqToBAPIFp(ofinfo, &some->value, builder);
        builder->appendChar(')');
    }
    
    template<typename T>
    void displayValue_Some(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const XSome<T>* some = (const XSome<T>*)valptr;

        os << "some(";
        ofinfo->opdispatch.displayFp(ofinfo, &some->value, os, indent);
        os << ")";
    }

    template <typename T>
    class XOption 
    {
    public:
        const TypeInfo* typeinfo;
        T data;
    
        static const TypeInfo* s_someTypeInfo;

    private:
        XOption(const TypeInfo* ti) : typeinfo{ti}, data{} { ; }
        XOption(const TypeInfo* ti, const T& d) : typeinfo{ti}, data{d} { ; }

    public:
        XOption() : typeinfo{}, data{} { ; };
        XOption(const XOption& other) = default;

        inline static XOption<T> none = XOption{&g_typeinfo_None};
        XOption(const XSome<T>& d) : typeinfo{s_someTypeInfo}, data{d.value} { ; }
        
        XBool isNone() const { return XBool::from(this->typeinfo == &g_typeinfo_None); }
        XBool isSome() const { return XBool::from(this->typeinfo != &g_typeinfo_None); }

        XNone asNone() const { return xnone; }
        XSome<T> asSome() const { return XSome<T>{this->data}; }
        T unwrap() const { return this->data; }

        XNone asNone() { return xnone; }
        XSome<T> asSome() { return XSome<T>{this->data}; }
        T unwrap() { return this->data; }

        friend XBool operator==(const XOption<T>& lhs, const XNone& rhs) { return lhs.isNone(); }
        friend XBool operator==(const XNone& lhs, const XOption<T>& rhs) { return rhs.isNone(); }
        friend XBool operator!=(const XOption<T>& lhs, const XNone& rhs) { return lhs.isSome(); }
        friend XBool operator!=(const XNone& lhs, const XOption<T>& rhs) { return rhs.isSome(); }
        
        friend XBool operator==(const XOption<T>& lhs, const T& rhs) { return lhs.isSome() & (lhs.data == rhs); }
        friend XBool operator==(const T& lhs, const XOption<T>& rhs) { return rhs.isSome() & (lhs == rhs.data); }
        friend XBool operator!=(const XOption<T>& lhs, const T& rhs) { return lhs.isNone() | (lhs.data != rhs); }
        friend XBool operator!=(const T& lhs, const XOption<T>& rhs) { return rhs.isNone() | (lhs != rhs.data); }
    };

    template<typename T>
    void jsonParseToBSQ_Option(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        if(j.is_null()) {
            *(XOption<T>*)resptr = XOption<T>::none;
        }
        else {
            const TypeInfo* someinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

            bsq_validate(j.is_array() && j.size() == 2, "JSON -> BSQ", 0, nullptr, "Expected JSON envelope for some<T>");
            bsq_validate(j[0] == "some" || j[0] == someinfo->typekey, "JSON -> BSQ", 0, nullptr, "Expected 'some' keyword or full type in JSON envelope for some<T>");

            XSome<T> val;
            someinfo->opdispatch.jsonParseToBSQFp(someinfo, j, &val);

            *(XOption<T>*)resptr = XOption<T>{val};
        }
    }

    template<typename T>
    void parseToBSQ_Option(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        if(lexer->testIsNone())
        {
            *(XOption<T>*)resptr = XOption<T>::none;
            return;
        }
        else {
            const TypeInfo* sominfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

            XSome<T> val;
            sominfo->opdispatch.parseToBSQFp(sominfo, lexer, &val);

            *(XOption<T>*)resptr = XOption<T>{val};
        }
    }

    template<typename T>
    json bsqToJSON_Option(const TypeInfo* tinfo, const void* valptr)
    {
        const XOption<T>* opt = (const XOption<T>*)valptr;
        if(opt->isNone()) {
            return nullptr;
        }
        else {
            const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
            return json::array({ "some", ofinfo->opdispatch.bsqToJSONFp(ofinfo, &opt->data) });
        }
    }

    template<typename T>
    void bsqToBAPI_Option(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const XOption<T>* opt = (const XOption<T>*)valptr;
        if(opt->isNone()) {
            builder->appendConstString("none");
        }
        else {
            const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
            builder->appendConstString("some");
            builder->appendChar('(');
            ofinfo->opdispatch.bsqToBAPIFp(ofinfo, &opt->data, builder);
            builder->appendChar(')');
        }
    }
    
    template<typename T>
    void displayValue_Option(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const XOption<T>* opt = (const XOption<T>*)valptr;
        if(opt->isNone()) {
            os << "none";
        }
        else {
            const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
            os << "some(";
            ofinfo->opdispatch.displayFp(ofinfo, &opt->data, os, indent);
            os << ")";
        }
    }

    //
    //TODO: probably want to specialize for option bool, nat/int where we can steal a indicator bit
    //TODO: Any Option<BoxedUnion> is interesting too (particularly for common case of string), where can can include none in the typeinfo
    //

    template <ConceptUnionRepr U>
    class BoxedUnion 
    {
    public:
        static_assert(std::is_union_v<U>, "BoxedUnion requires a union type U");
    
        const TypeInfo* typeinfo;
        U data;

    public:
        BoxedUnion() : typeinfo{}, data{} { ; }
        BoxedUnion(const TypeInfo* ti, const U& d) : typeinfo{ti}, data{d} { ; }
        BoxedUnion(const BoxedUnion& other) = default;

        BoxedUnion(const TypeInfo* ti, const uint8_t* dbegin, const uint8_t* dend) : typeinfo{ti} 
        { 
            std::copy(dbegin, dend, this->data.getUP());
        }

        // Note -- inject and extract are generated for each use based on the generation union type (see strings for example)

        XBool isTypeOf(const TypeInfo* ti) const { return XBool::from(this->typeinfo == ti); }
        XBool isNotTypeOf(const TypeInfo* ti) const { return XBool::from(this->typeinfo != ti); }

        XBool isSubtypeOf(const TypeInfo* ti) const { return ᐸRuntimeᐳ::isSubtypeOf(this->typeinfo, ti); }
        XBool isNotSubtypeOf(const TypeInfo* ti) const { return ᐸRuntimeᐳ::isNotSubtypeOf(this->typeinfo, ti); }

        template<typename V>
        BoxedUnion<V> convert() const 
        {
            static_assert(std::is_union_v<V>, "BoxedUnion convert requires a union type V");
            constexpr size_t copysize = std::min(sizeof(U), sizeof(V));

            return BoxedUnion<V>(this->typeinfo, this->data.getUP(), this->data.getUP() + copysize);
        }

        template<typename T, size_t idx>
        T accessfield() const 
        {
            if(this->typeinfo->tag != LayoutTag::Ref) {
                //not a pointer, just load the slot index as T
                return *(reinterpret_cast<const T*>(reinterpret_cast<uint64_t*>(const_cast<U*>(&this->data)) + idx));
            }
            else {
                assert(this->typeinfo->tag == LayoutTag::Ref);

                //dereference pointer in the union and then get the slot at index
                const uint64_t* ptrslots = *reinterpret_cast<const uint64_t**>(const_cast<U*>(&this->data));
                return *(reinterpret_cast<const T*>(ptrslots + idx));
            }
        }

        template<typename T>
        T accessfield(size_t idx) const 
        {
            if(this->typeinfo->tag != LayoutTag::Ref) {
                //not a pointer, just load the slot index as T
                return *(reinterpret_cast<const T*>(reinterpret_cast<uint64_t*>(const_cast<U*>(&this->data)) + idx));
            }
            else {
                assert(this->typeinfo->tag == LayoutTag::Ref);
                
                //dereference pointer in the union and then get the slot at index
                const uint64_t* ptrslots = *reinterpret_cast<const uint64_t**>(const_cast<U*>(&this->data));
                return *(reinterpret_cast<const T*>(ptrslots + idx));
            }
        }
    };
}
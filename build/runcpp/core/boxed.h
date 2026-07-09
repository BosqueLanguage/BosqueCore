#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bools.h"

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

    using XNone = uint64_t;
    constexpr XNone xnone = 0ull;

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
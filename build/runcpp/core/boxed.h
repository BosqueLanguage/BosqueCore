#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bools.h"

namespace ᐸRuntimeᐳ
{
    using XNone = uint64_t;
    constexpr XNone xnone = 0ull;

    template <typename T>
    class XSome 
    {
    public:
        T value;
        
        friend constexpr XBool operator==(const XSome<T>& lhs, const T& rhs) { return XBool::from(lhs.value == rhs); }
        friend constexpr XBool operator==(const T& lhs, const XSome<T>& rhs) { return XBool::from(lhs == rhs.value); }
        friend constexpr XBool operator!=(const XSome<T>& lhs, const T& rhs) { return XBool::from(lhs.value != rhs); }
        friend constexpr XBool operator!=(const T& lhs, const XSome<T>& rhs) { return XBool::from(lhs != rhs.value); }
    };

    template <typename T>
    class XOption 
    {
    public:
        const TypeInfo* typeinfo;
        T data;
    
    private:
        constexpr XOption(const TypeInfo* ti) : typeinfo(ti), data() {}
        constexpr XOption(const TypeInfo* ti, const T& d) : typeinfo(ti), data(d) {}

    public:
        constexpr XOption() : typeinfo(nullptr), data() {};
        constexpr XOption(const XOption& other) = default;
        
        // Special none option bits
        constexpr bool isNone() const { return this->typeinfo == &g_typeinfo_None; }
        static constexpr XOption<T> optnone = XOption(&g_typeinfo_None);
        
        // Some option bits
        constexpr bool isSome() const { return this->typeinfo != &g_typeinfo_None; }
        static XOption<T> fromSome(const TypeInfo* ti, const XSome<T>& d) { return XOption<T>(ti, d.value); }

        constexpr XNone safe_none() const { return xnone; }
        constexpr XSome<T> safe_some() const { return XSome<T>{this->data}; }
        constexpr T safe_unwrap() const { return this->data; }

        friend constexpr XBool operator==(const XOption<T>& lhs, const XNone& rhs) { return XBool::from(lhs.isNone()); }
        friend constexpr XBool operator==(const XNone& lhs, const XOption<T>& rhs) { return XBool::from(rhs.isNone()); }
        friend constexpr XBool operator!=(const XOption<T>& lhs, const XNone& rhs) { return XBool::from(lhs.isSome()); }
        friend constexpr XBool operator!=(const XNone& lhs, const XOption<T>& rhs) { return XBool::from(rhs.isSome()); }
        
        friend constexpr XBool operator==(const XOption<T>& lhs, const T& rhs) { return XBool::from(lhs.isSome() && lhs.data == rhs); }
        friend constexpr XBool operator==(const T& lhs, const XOption<T>& rhs) { return XBool::from(rhs.isSome() && lhs == rhs.data); }
        friend constexpr XBool operator!=(const XOption<T>& lhs, const T& rhs) { return XBool::from(lhs.isNone() || lhs.data != rhs); }
        friend constexpr XBool operator!=(const T& lhs, const XOption<T>& rhs) { return XBool::from(rhs.isNone() || lhs != rhs.data); }
    };

    //
    //TODO: probably want to specialize for option bool, nat/int where we can steal a indicator bit
    //TODO: Any Option<BoxedUnion> is interesting too (particularly for common case of string), where can can include none in the typeinfo
    //

    template <ConceptUnionRepr U>
    class BoxedUnion 
    {
    public:
        const TypeInfo* typeinfo;
        U data;

    private:
        static_assert(std::is_union_v<U>, "BoxedUnion requires a union type U");
        constexpr BoxedUnion(const TypeInfo* ti) : typeinfo(ti), data() {}

    public:
        constexpr BoxedUnion() : typeinfo(nullptr), data() {};
        constexpr BoxedUnion(const TypeInfo* ti, const U& d) : typeinfo(ti), data(d) {}
        constexpr BoxedUnion(const BoxedUnion& other) = default;
        
        // Note -- inject and extract are generated for each use based on the generation union type (see strings for example)

        template<typename V>
        BoxedUnion<V> convert() const 
        {
            static_assert(std::is_union_v<V>, "BoxedUnion convert requires a union type V");
            constexpr size_t copysize = std::min(sizeof(U), sizeof(V));

            BoxedUnion<V> cu(this->typeinfo);
            std::copy(reinterpret_cast<const uint8_t*>(&this->data), reinterpret_cast<const uint8_t*>(&this->data) + copysize, reinterpret_cast<uint8_t*>(&cu.data));
            
            return cu;
        }

        template<typename T, size_t idx>
        T accessfield() const 
        {
            if(this->typeinfo->tag != LayoutTag::Ref) {
                //not a pointer, just load the slot index as T
                return *(reinterpret_cast<const T*>(reinterpret_cast<const uint64_t*>(&this->data) + idx));
            }
            else {
                //dereference pointer in the union and then get the slot at index

                return *(reinterpret_cast<const T*>(reinterpret_cast<const uint64_t*>(this->data) + idx));
            }
        }

        template<typename T>
        T accessfield(size_t idx) const 
        {
            if(this->typeinfo->tag != LayoutTag::Ref) {
                //not a pointer, just load the slot index as T
                return *(reinterpret_cast<const T*>(reinterpret_cast<const uint64_t*>(&this->data) + idx));
            }
            else {
                //dereference pointer in the union and then get the slot at index

                return *(reinterpret_cast<const T*>(reinterpret_cast<const uint64_t*>(this->data) + idx));
            }
        }
    };
}
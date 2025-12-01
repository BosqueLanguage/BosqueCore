#pragma once

#include "common.h"
#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    template <typename T>
    class Option 
    {
    public:
        const TypeInfoBase* typeinfo;
        T data;
    
    private:
        constexpr Option(const TypeInfoBase* ti) : typeinfo(ti), data() {}
        constexpr Option(const TypeInfoBase* ti, const T& d) : typeinfo(ti), data(d) {}

    public:
        constexpr Option() : typeinfo(nullptr), data() {};
        constexpr Option(const Option& other) = default;
        
        // Special none option bits
        constexpr bool isNone() const { return this->typeinfo == &g_typeinfo_None; }
        static constexpr Option<T> optnone = Option(&g_typeinfo_None);

        // Some option bits
        constexpr bool isSome() const { return this->typeinfo != &g_typeinfo_None; }

        static Option<T> makeSome(const TypeInfoBase* ti, const T& d) { return Option<T>(ti, d); }
    };

    //
    //TODO: probably want to specialize for option bool, nat/int where we can steal a indicator bit
    //TODO: Any Option<BoxedUnion> is interesting too (particularly for common case of string), where can can include none in the typeinfo
    //

    template <ConceptUnionRepr U>
    class BoxedUnion 
    {
    public:
        const TypeInfoBase* typeinfo;
        U data;

    private:
        static_assert(std::is_union_v<U>, "BoxedUnion requires a union type U");
        constexpr BoxedUnion(const TypeInfoBase* ti) : typeinfo(ti), data() {}

    public:
        constexpr BoxedUnion() : typeinfo(nullptr), data() {};
        constexpr BoxedUnion(const TypeInfoBase* ti, const U& d) : typeinfo(ti), data(d) {}
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
#pragma once

#include "common.h"
#include "bsqtype.h"

namespace Core 
{
    namespace ᐸRuntimeᐳ
    {
        template <typename T>
        class Option 
        {
        public:
            const TypeInfoBase* typeinfo;
            T data;
        
        private:
            constexpr Option(const TypeInfoBase* ti) noexcept : typeinfo(ti), data() {}
            constexpr Option(const TypeInfoBase* ti, const T& d) noexcept : typeinfo(ti), data(d) {}

        public:
            constexpr Option() noexcept : typeinfo(nullptr), data() {};
            constexpr Option(const Option& other) noexcept = default;
            
            // Special none option bits
            constexpr bool isNone() const noexcept { return this->typeinfo == &g_wellKnownTypeNone; }
            static constexpr Option<T> optnone = Option(&g_wellKnownTypeNone);

            // Some option bits
            constexpr bool isSome() const noexcept { return this->typeinfo != &g_wellKnownTypeNone; }
            constexpr static Option<T> makeSome(const TypeInfoBase* ti, const T& d) noexcept { return Option(ti, d); }
        };

        //
        //TODO: probably want to specialize for option bool, nat/int where we can steal a indicator bit
        //TODO: Any Option<BoxedUnion> is interesting too (particularly for common case of string), where can can include none in the typeinfo
        //

        template <typename U>
        class BoxedUnion
        {
        public:
            const TypeInfoBase* typeinfo;
            U data;

        private:
            static_assert(std::is_union_v<U>, "BoxedUnion requires a union type U");
            constexpr BoxedUnion(const TypeInfoBase* ti) noexcept : typeinfo(ti), data() {}

        public:
            constexpr BoxedUnion() noexcept : typeinfo(nullptr), data() {};
            constexpr BoxedUnion(const TypeInfoBase* ti, const U& d) noexcept : typeinfo(ti), data(d) {}
            constexpr BoxedUnion(const BoxedUnion& other) noexcept = default;
            
            template<typename V>
            constexpr BoxedUnion<V> convert() const noexcept 
            {
                static_assert(std::is_union_v<V>, "BoxedUnion widen requires a union type V");
                static_assert(sizeof(V) == sizeof(U), "BoxedUnion widen requires V to be at least as large as U");

                BoxedUnion<V> cu(this->typeinfo);
                std::copy(reinterpret_cast<const uint8_t*>(&this->data), reinterpret_cast<const uint8_t*>(&this->data) + sizeof(U), reinterpret_cast<uint8_t*>(&cu.data));

                return cu;
            }

            template<typename V>
            BoxedUnion<V> widen() const noexcept 
            {
                static_assert(std::is_union_v<V>, "BoxedUnion widen requires a union type V");
                static_assert(sizeof(V) > sizeof(U), "BoxedUnion widen requires V to be at least as large as U");

                BoxedUnion<V> cw(this->typeinfo);
                std::copy(reinterpret_cast<const uint8_t*>(&this->data), reinterpret_cast<const uint8_t*>(&this->data) + sizeof(U), reinterpret_cast<uint8_t*>(&cw.data));

                return cw;
            }

            template<typename V>
            BoxedUnion<V> narrow() const noexcept 
            {
                static_assert(std::is_union_v<V>, "BoxedUnion widen requires a union type V");
                static_assert(sizeof(V) < sizeof(U), "BoxedUnion widen requires V to be at most as large as U");

                BoxedUnion<V> cn(this->typeinfo);
                std::copy(reinterpret_cast<const uint8_t*>(&this->data), reinterpret_cast<const uint8_t*>(&this->data) + sizeof(V), reinterpret_cast<uint8_t*>(&cn.data));

                return cn;
            }

            template<typename T, size_t idx>
            T accessfield() const noexcept 
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
            T accessfield(size_t idx) const noexcept 
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
}
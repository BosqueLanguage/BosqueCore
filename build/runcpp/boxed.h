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
            constexpr Option() noexcept : typeinfo(nullptr), data{0} {};
            constexpr Option(const Option& other) noexcept = default;
            constexpr Option& operator=(const Option& other) noexcept = default;
            
            // Special none option bits
            constexpr isNone() const noexcept { return this->typeinfo == &g_wellKnownTypeNone; }
            static constexpr Option optnone(&g_wellKnownTypeNone);

            // Some option bits
            constexpr isSome() const noexcept { return this->typeinfo != &g_wellKnownTypeNone; }
            constexpr makeSome(const TypeInfoBase* ti, const T& d) noexcept : typeinfo(ti) { return Option(ti, d); }
        };

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
            constexpr BoxedUnion& operator=(const BoxedUnion& other) noexcept = default;
            
            template<typename V>
            constexpr BoxedUnion<V> convert() noexcept {
                static_assert(std::is_union_v<V>, "BoxedUnion widen requires a union type V");
                static_assert(sizeof(V) == sizeof(U), "BoxedUnion widen requires V to be at least as large as U");

                return BoxedUnion<V>(this->typeinfo, std::bit_cast<V>(this->data));
            }

            template<typename V>
            constexpr BoxedUnion<V> widen() noexcept {
                static_assert(std::is_union_v<V>, "BoxedUnion widen requires a union type V");
                static_assert(sizeof(V) > sizeof(U), "BoxedUnion widen requires V to be at least as large as U");

                return BoxedUnion<V>(this->typeinfo, std::bit_cast<V>(this->data));
            }

            template<typename V>
            constexpr BoxedUnion<V> narrow() noexcept {
                static_assert(std::is_union_v<V>, "BoxedUnion widen requires a union type V");
                static_assert(sizeof(V) < sizeof(U), "BoxedUnion widen requires V to be at least as large as U");

                return BoxedUnion<V>(this->typeinfo, std::bit_cast<V>(this->data));
            }

            template<typename T, size_t idx, typename FTypeRepr>
            constexpr T access() noexcept { 
                constexpr if(std::is_pointer_v<FTypeRepr>) {
                    return *(reinterpret_cast<T*>(reinterpret_cast<uint64_t*>(this->data[0]) + i));   
                }
                else {
                    //load the field as if it is laid out inline
                    return *(reinterpret_cast<T*>(this->data + i));
                }
            }
        };
    }
}
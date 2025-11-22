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

        public:
            constexpr BoxedUnion() noexcept : typeinfo(nullptr), data() {};
            constexpr BoxedUnion(const TypeInfoBase* ti, const U& d) noexcept : typeinfo(ti), data(d) {}
            constexpr BoxedUnion(const BoxedUnion& other) noexcept = default;
            constexpr BoxedUnion& operator=(const BoxedUnion& other) noexcept = default;
            
            template<typename T>
            constexpr T access() noexcept { 
                constexpr if(std::is_pointer_v<T>) {
                    //load the field as if it is stored indirectly
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
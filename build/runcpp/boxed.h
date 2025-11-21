#pragma once

#include "common.h"
#include "bsqtype.h"

namespace Core 
{
    namespace ᐸRuntimeᐳ
    {
        template <size_t K>
        class Option 
        {
        public:
            TypeInfoBase* typeinfo;
            
        private:
            uint64_t data[K];

        public:
            constexpr Option() noexcept : typeinfo(nullptr), data{0} {};
            constexpr Option(const TypeInfoBase* ti) noexcept : typeinfo(ti), data{0} {};
            
            constexpr Option(const Option& rhs) noexcept = default;
            constexpr Option& operator=(const Option& rhs) noexcept = default;
            
            // Special none option constructor
            static constexpr Option optnone(&g_wellKnownTypeNone);

            // Some constructors
            template<typename T>
            constexpr makeSome(const TypeInfoBase* ti, const T& d) noexcept : typeinfo(ti) {
                static_assert(sizeof(T) <= K * sizeof(uint64_t), "Object too large for Option<K>");

                Option<K> opt(ti);
                *(reinterpret_cast<T*>(opt.data)) = d;
                return opt;
            }

            template<typename T>
            constexpr T get() {
                return *(reinterpret_cast<T*>(this->data));
            }
        };

        template <size_t K>
        class Boxed 
        {
        public:
            const TypeInfoBase* typeinfo;
            
        private:
            const uint64_t data[K];

        public:
            constexpr Boxed() noexcept : typeinfo(nullptr), data{0} {};
            constexpr Boxed(const TypeInfoBase* ti) noexcept : typeinfo(ti), data{0} {};

            constexpr Boxed(const Boxed& rhs) noexcept = default;
            constexpr Boxed& operator=(const Boxed& rhs) noexcept {
                this->typeinfo = rhs.typeinfo;
                std::copy(rhs.data, rhs.data + K, const_cast<uint64_t*>(this->data));
                return *this;
            }

            // Empty constructor
            constexpr Boxed(const TypeInfoBase* ti) noexcept : typeinfo(ti), data{0} {}

            // Value constructors
            template<typename T>
            static constexpr Boxed makeBoxed(const TypeInfoBase* ti, const T& d) noexcept {
                static_assert(sizeof(T) <= K * sizeof(uint64_t), "Object too large for Boxed<K>");

                constexpr Boxed<K> boxed(ti);
                //*(reinterpret_cast<T*>(boxed.data)) = d;
                return boxed;
            }

            template<typename T, size_t i=0>
            constexpr T access() noexcept { 
                if(this->typeinfo->tag == LayoutTag::Ref) {
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
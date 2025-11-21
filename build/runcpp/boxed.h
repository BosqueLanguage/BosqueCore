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
            uintptr_t data[K];

        public:
            constexpr Option() noexcept : typeinfo(nullptr), data{0} {};
            constexpr Option(const Option& rhs) noexcept = default;
            constexpr Option(Option&& rhs) noexcept = default;

            Option& operator=(const Option& rhs) noexcept = default;
            Option& operator=(Option&& rhs) noexcept = default;

            // Empty constructor
            constexpr Option(TypeInfoBase* ti) noexcept : typeinfo(ti), data{0} {}

            // Value constructors
            template<typename T>
            inline constexpr Option(TypeInfoBase* ti, const T& d) noexcept : typeinfo(ti) {
                static_assert(sizeof(T) <= K * sizeof(uintptr_t), "Object too large for Option<K>");
                *(reinterpret_cast<T*>(this->data)) = d;
            }

            // Value constructors
            template<typename T>
            inline constexpr Option(TypeInfoBase* ti, T&& d) noexcept : typeinfo(ti) {
                static_assert(sizeof(T) <= K * sizeof(uintptr_t), "Object too large for Option<K>");
                *(reinterpret_cast<T*>(this->data)) = d;
            }

            template<typename T, uintptr_t i=0>
            inline constexpr T access() noexcept { 
                if(this->typeinfo->tag == LayoutTag::Ref) {
                    //load the field as if it is stored indirectly
                    return *(reinterpret_cast<T*>(reinterpret_cast<uintptr_t*>(this->data[0]) + i));   
                }
                else {
                    //load the field as if it is laid out inline
                    return *(reinterpret_cast<T*>(this->data + i));
                }
            }

            constexpr uintptr_t accessnone() noexcept { return UINTPTR_MAX; }
        };

        template <size_t K>
        class Boxed 
        {
        public:
            TypeInfoBase* typeinfo;
            
        private:
            uintptr_t data[K];

        public:
            constexpr Boxed() noexcept : typeinfo(nullptr), data{0} {};
            constexpr Boxed(const Boxed& rhs) noexcept = default;
            constexpr Boxed(Boxed&& rhs) noexcept = default;

            Boxed& operator=(const Boxed& rhs) noexcept = default;
            Boxed& operator=(Boxed&& rhs) noexcept = default;

            // Empty constructor
            constexpr Boxed(TypeInfoBase* ti) noexcept : typeinfo(ti), data{0} {}

            // Value constructors
            template<typename T>
            inline constexpr Boxed(TypeInfoBase* ti, const T& d) noexcept : typeinfo(ti) {
                static_assert(sizeof(T) <= K * sizeof(uintptr_t), "Object too large for Boxed<K>");
                *(reinterpret_cast<T*>(this->data)) = d;
            }

            // Value constructors
            template<typename T>
            inline constexpr Boxed(TypeInfoBase* ti, T&& d) noexcept : typeinfo(ti) {
                static_assert(sizeof(T) <= K * sizeof(uintptr_t), "Object too large for Boxed<K>");
                *(reinterpret_cast<T*>(this->data)) = d;
            }

            template<typename T, uintptr_t i=0>
            inline constexpr T access() noexcept { 
                if(this->typeinfo->tag == LayoutTag::Ref) {
                    //load the field as if it is stored indirectly
                    return *(reinterpret_cast<T*>(reinterpret_cast<uintptr_t*>(this->data[0]) + i));   
                }
                else {
                    //load the field as if it is laid out inline
                    return *(reinterpret_cast<T*>(this->data + i));
                }
            }
        };

    template<typename T, uintptr_t E>
    T vlookup(const __CoreGC::FieldOffsetInfo* vtable) noexcept {
        if(this->typeinfo->tag == __CoreGC::Tag::Ref) {
            return *reinterpret_cast<T*>(this->data[static_cast<uintptr_t>(vtable[E].byteoffset)]);
        }
        else {
            return *reinterpret_cast<T*>(this->data + static_cast<uintptr_t>(vtable[E].byteoffset));
        }
    }
};

template<>
class Boxed<1> {
public:
    __CoreGC::TypeInfoBase* typeinfo = nullptr;
    uintptr_t data = 0;

    Boxed() noexcept = default;
    Boxed(const Boxed& rhs) noexcept = default;
    Boxed& operator=(const Boxed& rhs) noexcept = default;

    template<typename T>
    Boxed(__CoreGC::TypeInfoBase* ti, T&& d) noexcept : typeinfo(ti), data(*reinterpret_cast<uintptr_t*>(&d)) { 
        static_assert(sizeof(T) <= sizeof(uintptr_t), "Object too large for Boxed<1>");
    };

    // None constructor
    Boxed(__CoreGC::TypeInfoBase* ti) noexcept : typeinfo(ti) {};

    template<typename T, uintptr_t I=0>
    constexpr T* access_ref() noexcept {
        return reinterpret_cast<T*>(reinterpret_cast<uintptr_t*>(this->data) + I);   
    }

    template<typename T, uintptr_t I=0>
    constexpr T access() noexcept { 
        if (this->typeinfo->tag == __CoreGC::Tag::Ref) {
            return *access_ref<T, I>();
        }
        else {
            return *reinterpret_cast<T*>(&this->data);
        }
    }
    
    constexpr uintptr_t accessnone() noexcept { return UINTPTR_MAX; }
};

template<>
class Boxed<0> {
public:
    __CoreGC::TypeInfoBase* typeinfo = nullptr;

    Boxed() noexcept = default;
    Boxed(const Boxed& rhs) noexcept = default;
    Boxed& operator=(const Boxed& rhs) noexcept = default;        

    Boxed(__CoreGC::TypeInfoBase* ti) noexcept: typeinfo(ti) {};

    template<typename T>
    constexpr T access() noexcept { 
        return T{};
    }
};
    }
}
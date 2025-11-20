#pragma once

#include "common.h"
#include "bsqtype.h"

namespace Core 
{
    namespace ᐸRuntimeᐳ
    {
        template <size_t K>
        class Boxed 
        {
        public:
            TypeInfoBase* typeinfo;
            
        private:
            uintptr_t data[K];

        public:
            TypeInfoBase* typeinfo = nullptr;
            uintptr_t data[K] = {};

            constexpr Boxed() noexcept : typeinfo(nullptr), data{0} {};
            constexpr Boxed(const Boxed& rhs) noexcept = default;
            constexpr Boxed(Boxed&& rhs) noexcept = default;

            Boxed& operator=(const Boxed& rhs) noexcept = default;
            Boxed& operator=(Boxed&& rhs) noexcept = default;

            // Empty constructor
            constexpr Boxed(TypeInfoBase* ti) noexcept : typeinfo(ti), data{0} {}

            // Value constructors
            template<typename T>
            constexpr Boxed(TypeInfoBase* ti, const T& d) noexcept : typeinfo(ti) {
                static_assert(sizeof(T) <= K * sizeof(uintptr_t), "Object too large for Boxed<K>");
                *(reinterpret_cast<T*>(this->data)) = d;
            };

            // Value constructors
            template<typename T>
            constexpr Boxed(TypeInfoBase* ti, T&& d) noexcept : typeinfo(ti) {
                static_assert(sizeof(T) <= K * sizeof(uintptr_t), "Object too large for Boxed<K>");
                *(reinterpret_cast<T*>(this->data)) = d;
            };

            template<typename T, uintptr_t I=0>
            constexpr T* access_ref() noexcept {
                return reinterpret_cast<T*>(reinterpret_cast<uintptr_t*>(this->data[0]) + I);   
            }

    template<typename T, uintptr_t I=0>
    constexpr T access() noexcept { 
        if(this->typeinfo->tag == __CoreGC::Tag::Ref) {
            return *access_ref<T, I>();
        }
        else {
            return *reinterpret_cast<T*>(&this->data[I]);
        }
    }

    constexpr uintptr_t accessnone() noexcept { return UINTPTR_MAX; }

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
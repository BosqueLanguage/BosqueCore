#pragma once

#include "../common.h"

namespace Core 
{
    class Nat
    {
    public:
        static constexpr uint64_t MAX_NAT = 4611686018427387903ull; 

    private:
        uint64_t value;

        inline constexpr static bool isValidNat(uint64_t v) noexcept
        {
            return v <= Nat::MAX_NAT;
        }

    public:
        constexpr Nat() noexcept : value(0) {}
        constexpr Nat(uint64_t v) noexcept : value(v) {}
        constexpr Nat(const Nat& other) noexcept = default;
        constexpr Nat(Nat&& other) noexcept = default;
        ~Nat() noexcept = default;

        constexpr Nat& operator=(const Nat& other) noexcept = default;
        constexpr Nat& operator=(Nat&& other) noexcept = default;

        // Overloaded operators on Nat
        constexpr Nat& operator+=(const Nat&rhs) noexcept
        {
            if(__builtin_add_overflow(this->value, rhs.value, &this->value) || !Nat::isValidNat(this->value)) { BSQ_ABORT; }
            return *this;
        }

        constexpr Nat& operator-=(const Nat &rhs) noexcept
        {
            if(__builtin_sub_overflow(this->value, rhs.value, &this->value) || !Nat::isValidNat(this->value)) { BSQ_ABORT; }
            return *this;
        }
        constexpr Nat& operator/=(const Nat &rhs) noexcept
        {
            if(rhs.value == 0) { BSQ_ABORT; }
            this->value /= rhs.value;
            return *this;
        }
        constexpr Nat& operator*=(const Nat &rhs) noexcept
        {
            if(__builtin_mul_overflow(this->value, rhs.value, &this->value) || !Nat::isValidNat(this->value)) { BSQ_ABORT; }
            return *this;
        }

        constexpr Nat operator+() const noexcept
        {
            return Nat{this->value};
        }
        constexpr Nat operator-() const noexcept
        {
            return Nat{-this->value};
        }

        friend constexpr Nat operator+(Nat lhs, const Nat &rhs) noexcept
        {
            return lhs += rhs;
        }
        friend constexpr Nat operator-(Nat lhs, const Nat &rhs) noexcept
        {
            return lhs -= rhs;
        }
        friend constexpr Nat operator/(Nat lhs, const Nat &rhs) noexcept
        {
            return lhs /= rhs;
        }
        friend constexpr Nat operator*(Nat lhs, const Nat &rhs) noexcept
        {
            return lhs *= rhs;
        }
        friend constexpr bool operator<(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const Nat &lhs, const Nat &rhs) noexcept { return rhs < lhs; }
        friend constexpr bool operator!=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs == rhs); }
        friend constexpr bool operator<=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs > rhs); }
        friend constexpr bool operator>=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs < rhs); }
    };

    class Int
    {
    public:
    };

    class BigNat
    {
    public:
    };

    class BigInt
    {
    public:
    };

    inline constexpr Nat operator""_Nat(unsigned long long n)
    {
        return Nat{n};
    }
}

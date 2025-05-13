#pragma once

#include <stdint.h>
#include <iostream>
#include <cmath>

namespace __CoreCpp {

constexpr bool is_valid_int(int64_t val) {
    return ((val >= -(1LL << 62)) && (val <= (1LL << 62) - 1));
}

constexpr bool is_valid_bigint(__int128_t val) {
    return ((val >= -(__int128_t(1) << 126)) && (val <= (__int128_t(1) << 126) - 1));
}

constexpr bool is_valid_nat(uint64_t val) {
    return (val <= (1ULL << 63) - 1);
}

constexpr bool is_valid_bignat(__uint128_t val) {
    return (val <= (__uint128_t(1) << 127) - 1);
}

// Signed 63 bit value
class Int {
    int64_t value;
    constexpr explicit Int(int64_t val) : value(val){ 
        if(!is_valid_int(val)) {
            throw std::runtime_error("Invalid size for 63 bit int literal!\n");
        }
    }; 
public:
    constexpr Int() noexcept : value(0) {};
    constexpr int64_t get() const noexcept { return value; }

    // "_i" postfix is overloaded to call from_literal
    static constexpr Int from_literal(int64_t v) { return Int(v); }

    // Overloaded operations on Int
    constexpr Int operator+(Int const& i1) { return Int(value + i1.value); }
    constexpr Int operator-(Int const& i1) { return Int(value - i1.value); }
    constexpr Int operator/(Int const& i1) { return Int(value / i1.value); }
    constexpr Int operator*(Int const& i1) { return Int(value * i1.value); }
    constexpr bool operator==(Int const& i1) const { return value == i1.value; }
    constexpr bool operator!=(Int const& i1) const { return value != i1.value; }
    constexpr bool operator<(Int const& i1) const { return value < i1.value; }
    constexpr bool operator<=(Int const& i1) const { return value <= i1.value; }
    constexpr bool operator>(Int const& i1) const { return value > i1.value; }
    constexpr bool operator>=(Int const& i1) const { return value >= i1.value; }
};

// Signed 127 bit value
class BigInt {
    __int128_t value;
    constexpr explicit BigInt(int64_t val) : value(val){ 
        if(!is_valid_bigint(val)) {
            throw std::runtime_error("Invalid size for 127 bit int literal!\n");
        }
    }; 
public:
    constexpr BigInt() noexcept : value(0) {};
    constexpr __int128_t get() const noexcept { return value; }

    // "_I" postfix is overloaded to call from_literal
    static constexpr BigInt from_literal(__int128_t v) { return BigInt(v); }

    // Overloaded operators on BigInt 
    constexpr BigInt operator+(BigInt const& i1) { return BigInt(value + i1.value); }
    constexpr BigInt operator-(BigInt const& i1) { return BigInt(value - i1.value); }
    constexpr BigInt operator/(BigInt const& i1) { return BigInt(value / i1.value); }
    constexpr BigInt operator*(BigInt const& i1) { return BigInt(value * i1.value); }
    constexpr bool operator==(BigInt const& i1) const { return value == i1.value; }
    constexpr bool operator!=(BigInt const& i1) const { return value != i1.value; }
    constexpr bool operator<(BigInt const& i1) const { return value < i1.value; }
    constexpr bool operator<=(BigInt const& i1) const { return value <= i1.value; }
    constexpr bool operator>(BigInt const& i1) const { return value > i1.value; }
    constexpr bool operator>=(BigInt const& i1) const { return value >= i1.value; }
};

// Unsigned 63 bit value
class Nat {
    uint64_t value;
    constexpr explicit Nat(uint64_t val) : value(val) {
        if(!is_valid_nat(val)) {
            throw std::runtime_error("Invalid size for 63 bit nat literal!\n");
        }
    }; 
public:
    constexpr Nat() noexcept : value(0) {};
    constexpr int64_t get() const noexcept { return value; }

    // "_n" postfix is overloaded to call from_literal
    static constexpr Nat from_literal(int64_t v) { return Nat(v); }

    // Overloaded operators on Nat
    constexpr Nat operator+(Nat const& i1) { return Nat(value + i1.value); }
    constexpr Nat operator-(Nat const& i1) { return Nat(value - i1.value); }
    constexpr Nat operator/(Nat const& i1) { return Nat(value / i1.value); }
    constexpr Nat operator*(Nat const& i1) { return Nat(value * i1.value); }
    constexpr bool operator==(Nat const& i1) const { return value == i1.value; }
    constexpr bool operator!=(Nat const& i1) const { return value != i1.value; }
    constexpr bool operator<(Nat const& i1) const { return value < i1.value; }
    constexpr bool operator<=(Nat const& i1) const { return value <= i1.value; }
    constexpr bool operator>(Nat const& i1) const { return value > i1.value; }
    constexpr bool operator>=(Nat const& i1) const { return value >= i1.value; }
};

// Unsigned 127 bit value
class BigNat {
    __uint128_t value;
    constexpr explicit BigNat(__uint128_t val) : value(val) {
        if(!is_valid_bignat(val)) {
            throw std::runtime_error("Invalid size for 127 bit nat literal!\n");
        }
    }; 
public:
    constexpr BigNat() noexcept : value(0) {};
    constexpr __uint128_t get() const noexcept { return value; }

    // "_N" postfix is overloaded to call from_literal
    static constexpr BigNat from_literal(__uint128_t v) { return BigNat(v); }

    // Overloaded operators on BigNat
    constexpr BigNat operator+(BigNat const& i1) { return BigNat(value + i1.value); }
    constexpr BigNat operator-(BigNat const& i1) { return BigNat(value - i1.value); }
    constexpr BigNat operator/(BigNat const& i1) { return BigNat(value / i1.value); }
    constexpr BigNat operator*(BigNat const& i1) { return BigNat(value * i1.value); }
    constexpr bool operator==(BigNat const& i1) const { return value == i1.value; }
    constexpr bool operator!=(BigNat const& i1) const { return value != i1.value; }
    constexpr bool operator<(BigNat const& i1) const { return value < i1.value; }
    constexpr bool operator<=(BigNat const& i1) const { return value <= i1.value; }
    constexpr bool operator>(BigNat const& i1) const { return value > i1.value; }
    constexpr bool operator>=(BigNat const& i1) const { return value >= i1.value; }
};

// Are runtime checks necessary here?
// 64 bit base 2 floats
class Float {
    double value;
    constexpr explicit Float(double val) : value(val) { 
        if(!std::isfinite(val)) { 
            throw std::runtime_error("Bosque Float does now allow NAN/Infinity!\n");
        } 
    }
public:
    constexpr Float() noexcept : value(0) {};
    constexpr double get() const noexcept { return value; }

    // "_f" prefix is overloaded to call from_literal 
    static constexpr Float from_literal(double v) { return Float(v); }

    // Overloaded operators on float
    constexpr Float operator+(Float const& i1) { return Float(value + i1.value); }
    constexpr Float operator-(Float const& i1) { return Float(value - i1.value); }
    constexpr Float operator/(Float const& i1) { return Float(value / i1.value); }
    constexpr Float operator*(Float const& i1) { return Float(value * i1.value); }
    constexpr bool operator==(Float const& i1) const { return value == i1.value; }
    constexpr bool operator!=(Float const& i1) const { return value != i1.value; }
    constexpr bool operator<(Float const& i1) const { return value < i1.value; }
    constexpr bool operator<=(Float const& i1) const { return value <= i1.value; }
    constexpr bool operator>(Float const& i1) const { return value > i1.value; }
    constexpr bool operator>=(Float const& i1) const { return value >= i1.value; }
};

// Useful for keeping track of path in tree iteration
struct PathStack {
    uint64_t bits;
    int index;

    static PathStack create();
    PathStack left() const;
    PathStack right() const;
    PathStack up() const;
};

// We say for now no more than 8 chars, may want to make this dynamically pick 8 or 16 max
struct CCharBuffer {
    uint8_t chars[8];
    int size;

    static CCharBuffer create_empty();
    static CCharBuffer create_1(uint8_t c1);
    static CCharBuffer create_2(uint8_t c1, uint8_t c2);
    static CCharBuffer create_3(uint8_t c1, uint8_t c2, uint8_t c3);
    static CCharBuffer create_4(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4);
    static CCharBuffer create_5(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5);
    static CCharBuffer create_6(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5, uint8_t c6);
    static CCharBuffer create_7(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5, uint8_t c6, uint8_t c7);
    static CCharBuffer create_8(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5, uint8_t c6, uint8_t c7, uint8_t c8);
};

struct UnicodeCharBuffer {
    uint32_t chars[8];
    int size;

    static UnicodeCharBuffer create_empty();
    static UnicodeCharBuffer create_1(uint32_t c1);
    static UnicodeCharBuffer create_2(uint32_t c1, uint32_t c2);
    static UnicodeCharBuffer create_3(uint32_t c1, uint32_t c2, uint32_t c3);
    static UnicodeCharBuffer create_4(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4);
    static UnicodeCharBuffer create_5(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5);
    static UnicodeCharBuffer create_6(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5, uint32_t c6);
    static UnicodeCharBuffer create_7(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5, uint32_t c6, uint32_t c7);
    static UnicodeCharBuffer create_8(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5, uint32_t c6, uint32_t c7, uint32_t c8);
};

} // namespace __CoreCpp

constexpr __CoreCpp::Int operator"" _i(unsigned long long v) { return __CoreCpp::Int::from_literal(static_cast<int64_t>(v)); };
constexpr __CoreCpp::BigInt operator"" _I(unsigned long long v) { return __CoreCpp::BigInt::from_literal(static_cast<__int128_t>(v)); }; 
constexpr __CoreCpp::Nat operator"" _n(unsigned long long v) { return __CoreCpp::Nat::from_literal(static_cast<int64_t>(v)); };
constexpr __CoreCpp::BigNat operator"" _N(unsigned long long v) { return __CoreCpp::BigNat::from_literal(static_cast<__uint128_t>(v)); };
constexpr __CoreCpp::Float operator"" _f(long double v) { return __CoreCpp::Float::from_literal(static_cast<double>(v)); };
#pragma once

#include <stdint.h>
#include <iostream>
#include <cmath>

namespace __CoreCpp {

#define MAX_BSQ_INT ((int64_t(1) << 62) - 1)
#define MIN_BSQ_INT (-(int64_t(1) << 62) + 1) 
#define MAX_BSQ_BIGINT ((__int128_t(1) << 126) - 1)
#define MIN_BSQ_BIGINT (-(__int128_t(1) << 126) + 1)
#define MAX_BSQ_NAT ((uint64_t(1) << 63) - 1)
#define MAX_BSQ_BIGNAT ((__uint128_t(1) << 127) - 1)

constexpr bool is_valid_int(int64_t val) {
    return ((val >= MIN_BSQ_INT) && (val <= MAX_BSQ_INT));
}

constexpr bool is_valid_bigint(__int128_t val) {
    return ((val >= MIN_BSQ_BIGINT) && (val <= MAX_BSQ_BIGINT));
}

constexpr bool is_valid_nat(uint64_t val) {
    return (val <= MAX_BSQ_NAT);
}

constexpr bool is_valid_bignat(__uint128_t val) {
    return (val <= MAX_BSQ_BIGNAT);
}

//
// Note: It appears that our builtin arithmetic operations do not evaluate at compile time (not 100% but seems to be the case).
// This is why I decided to throw runtime errors. This might be fine - if we need to be able to detect at compile
// time we will likely need to add custom overflow checking functions.
//

// Signed 63 bit value
class Int {
    int64_t value;
public:
    //
    // TODO: Perhaps in place of this-> value we can just use value? need to look this up 
    // (in our members that is)
    //

    constexpr Int() noexcept : value(0) {};
    constexpr explicit Int(int64_t val) : value(val){ 
        if(!is_valid_int(val)) {
            throw std::runtime_error("Invalid size for 63 bit signed integer!\n");
        }
    }; 

    // Overloaded operations on Int
    constexpr Int& operator+=(const Int& rhs) {
        if(__builtin_add_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr Int& operator-=(const Int& rhs) {
        if(__builtin_sub_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr Int& operator/=(const Int& rhs) { // NOTE: Need to verify these checks
        if(this->value == 0 || (this->value == MIN_BSQ_INT && rhs.value == -1)) {
            throw std::runtime_error("Overflow detected on division of two 63 bit signed integers!\n");
        }
        this->value /= rhs.value;
        return *this;
    }
    constexpr Int& operator*=(const Int& rhs) {
        if(__builtin_mul_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr Int operator-() { // dont want to modify this here
        if(this->value == MIN_BSQ_INT) {
            throw std::runtime_error("Overflow detected when negating 63 bit signed integer!\n");
        }
        return Int(-this->value);
    }
    friend constexpr Int operator+(Int lhs, const Int& rhs) { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr Int operator-(Int lhs, const Int& rhs) { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr Int operator/(Int lhs, const Int& rhs) {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr Int operator*(Int lhs, const Int& rhs) {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const Int& lhs, const Int& rhs) { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const Int& lhs, const Int& rhs) { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const Int& lhs, const Int& rhs) { return rhs < lhs; }
    friend constexpr bool operator!=(const Int& lhs, const Int& rhs) { return !(lhs == rhs); }
    friend constexpr bool operator<=(const Int& lhs, const Int& rhs) { return !(lhs > rhs); }
    friend constexpr bool operator>=(const Int& lhs, const Int& rhs) { return !(lhs < rhs); }
};

// Signed 127 bit value
class BigInt {
    __int128_t value;
    //
    // TODO: Make these conversions some namespaced function
    //
    static constexpr __int128_t to_int128(const char* v) {
        __int128_t res = 0;  
        const char* p = v;

        while(*p >= '0' && *p <= '9') {
            res = (res * 10) + (*p - '0');
            p++;
        }

        return res;
    }
public:
    //
    // TODO: Same with int, check if we can just replace this->value with value
    //
    constexpr BigInt() noexcept : value(0) {};

    // Used when constructing from bosque code
    constexpr explicit BigInt(const char* val) : value(to_int128(val)) {
        if(!is_valid_bigint(value)) {
            throw std::runtime_error("Invalid size for 127 bit signed integer!\n");
        }
    };

    // Used with our arithmetic operators
    constexpr explicit BigInt(__int128_t val) : value(val) {
        if(!is_valid_bigint(val)) {
            throw std::runtime_error("Invalid size for 127 bit signed integer!\n");
        }
    }; 

    // Overloaded operators on BigInt
    constexpr BigInt& operator+=(const BigInt& rhs) {
        if(__builtin_add_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr BigInt& operator-=(const BigInt& rhs) {
        if(__builtin_sub_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr BigInt& operator/=(const BigInt& rhs) {
        if(this->value == 0 || (this->value == MIN_BSQ_BIGINT && rhs.value == -1)) {
            throw std::runtime_error("Overflow detected on division of two 127 bit signed integers!\n");
        }
        this->value /= rhs.value;
        return *this;
    }
    constexpr BigInt& operator*=(const BigInt& rhs) {
        if(__builtin_mul_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr BigInt operator-() { // dont want to modify this here
        if(this->value == MIN_BSQ_BIGINT) {
            throw std::runtime_error("Overflow detected when negating 127 bit signed integer!\n");
        }
        return BigInt(-this->value);
    }
    friend constexpr BigInt operator+(BigInt lhs, const BigInt& rhs) { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr BigInt operator-(BigInt lhs, const BigInt& rhs) { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr BigInt operator/(BigInt lhs, const BigInt& rhs) {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr BigInt operator*(BigInt lhs, const BigInt& rhs) {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const BigInt& lhs, const BigInt& rhs) { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const BigInt& lhs, const BigInt& rhs) { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const BigInt& lhs, const BigInt& rhs) { return rhs < lhs; }
    friend constexpr bool operator!=(const BigInt& lhs, const BigInt& rhs) { return !(lhs == rhs); }
    friend constexpr bool operator<=(const BigInt& lhs, const BigInt& rhs) { return !(lhs > rhs); }
    friend constexpr bool operator>=(const BigInt& lhs, const BigInt& rhs) { return !(lhs < rhs); } 
};

// Unsigned 63 bit value
class Nat {
    uint64_t value;
public:
    constexpr Nat() noexcept : value(0) {};
    constexpr explicit Nat(uint64_t val) : value(val) {
        if(!is_valid_nat(val)) {
            throw std::runtime_error("Invalid size for 63 bit unsigned integer!\n");
        }
    }; 

    // Overloaded operators on Nat
    constexpr Nat& operator+=(const Nat& rhs) {
        if(__builtin_add_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit  integers!\n");
        }
        return *this;       
    }
    constexpr Nat& operator-=(const Nat& rhs) {
        if(__builtin_sub_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr Nat& operator/=(const Nat& rhs) {
        if(rhs.value == 0) {
            throw std::runtime_error("Overflow detected on division of two 127 bit signed integers!\n");
        }
        this->value /= rhs.value;
        return *this;
    }
    constexpr Nat& operator*=(const Nat& rhs) {
        if(__builtin_mul_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    friend constexpr Nat operator+(Nat lhs, const Nat& rhs) { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr Nat operator-(Nat lhs, const Nat& rhs) { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr Nat operator/(Nat lhs, const Nat& rhs) {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr Nat operator*(Nat lhs, const Nat& rhs) {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const Nat& lhs, const Nat& rhs) { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const Nat& lhs, const Nat& rhs) { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const Nat& lhs, const Nat& rhs) { return rhs < lhs; }
    friend constexpr bool operator!=(const Nat& lhs, const Nat& rhs) { return !(lhs == rhs); }
    friend constexpr bool operator<=(const Nat& lhs, const Nat& rhs) { return !(lhs > rhs); }
    friend constexpr bool operator>=(const Nat& lhs, const Nat& rhs) { return !(lhs < rhs); } 
};

// Unsigned 127 bit value
class BigNat {
    __uint128_t value;
    static constexpr __uint128_t to_uint128(const char* v) {
        __uint128_t res = 0;

        const char* p = v;
        while(*p >= '0' && *p <= '9') {
            res = (res * 10) + (*p - '0');
            p++;
        }

        return res; 
    }

public:
    constexpr BigNat() noexcept : value(0) {};

    // Used when constructing from bosque code
    constexpr explicit BigNat(const char* val) : value(to_uint128(val)) {
        if(!is_valid_bignat(value)) {
            throw std::runtime_error("Invalid size for 127 bit unsigned integer!\n");
        }
    }; 

    // Used with our arithmetic operators
    constexpr explicit BigNat(__uint128_t val) : value(val) {
        if(!is_valid_bignat(val)) {
            throw std::runtime_error("Invalid size for 127 bit unsigned integer!\n");
        }
    };
    
    //
    // TODO: Same with int, check if we can just replace this->value with value
    //

    // Overloaded operators on BigInt
    constexpr BigNat& operator+=(const BigNat& rhs) {
        if(__builtin_add_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr BigNat& operator-=(const BigNat& rhs) {
        if(__builtin_sub_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    constexpr BigNat& operator/=(const BigNat& rhs) {
        if(this->value == 0) {
            throw std::runtime_error("Overflow detected on division of two 127 bit signed integers!\n");
        }
        this->value /= rhs.value;
        return *this;
    }
    constexpr BigNat& operator*=(const BigNat& rhs) {
        if(__builtin_mul_overflow(this->value, rhs.value, &this->value)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }
        return *this;       
    }
    friend constexpr BigNat operator+(BigNat lhs, const BigNat& rhs) { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr BigNat operator-(BigNat lhs, const BigNat& rhs) { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr BigNat operator/(BigNat lhs, const BigNat& rhs) {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr BigNat operator*(BigNat lhs, const BigNat& rhs) {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const BigNat& lhs, const BigNat& rhs) { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const BigNat& lhs, const BigNat& rhs) { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const BigNat& lhs, const BigNat& rhs) { return rhs < lhs; }
    friend constexpr bool operator!=(const BigNat& lhs, const BigNat& rhs) { return !(lhs == rhs); }
    friend constexpr bool operator<=(const BigNat& lhs, const BigNat& rhs) { return !(lhs > rhs); }
    friend constexpr bool operator>=(const BigNat& lhs, const BigNat& rhs) { return !(lhs < rhs); }
};

// 64 bit base 2 floats
class Float {
    double value;
public:
    constexpr Float() noexcept : value(0) {};
     constexpr explicit Float(double val) : value(val) { 
        if(!std::isfinite(val)) { 
            throw std::runtime_error("Bosque Float does not allow NAN/Infinity!\n");
        } 
    }

    static constexpr Float from_literal(double v) { return Float(v); }

    // Overloaded operations on Float
    constexpr Float& operator+=(const Float& rhs) {
        double res = this->value + rhs.value;
        if(!std::isfinite(res)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed Floategers!\n");
        }
        this->value = res;
        return *this;       
    }
    constexpr Float& operator-=(const Float& rhs) {
        double res = this->value - rhs.value;
        if(!std::isfinite(res)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed Floategers!\n");
        }
        this->value = res;
        return *this;
    }
    constexpr Float& operator/=(const Float& rhs) { // NOTE: Need to verify these checks
        double res = this->value / rhs.value;
        if(!std::isfinite(res)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed Floategers!\n");
        }
        this->value = res;
        return *this;
    }
    constexpr Float& operator*=(const Float& rhs) {
        double res = this->value * rhs.value;
        if(!std::isfinite(res)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed Floategers!\n");
        }
        this->value = res;
        return *this;       
    }
    constexpr Float operator-() { // dont want to modify this here
        return Float(-this->value);
    }
    friend constexpr Float operator+(Float lhs, const Float& rhs) { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr Float operator-(Float lhs, const Float& rhs) { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr Float operator/(Float lhs, const Float& rhs) {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr Float operator*(Float lhs, const Float& rhs) {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const Float& lhs, const Float& rhs) { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const Float& lhs, const Float& rhs) { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const Float& lhs, const Float& rhs) { return rhs < lhs; }
    friend constexpr bool operator!=(const Float& lhs, const Float& rhs) { return !(lhs == rhs); }
    friend constexpr bool operator<=(const Float& lhs, const Float& rhs) { return !(lhs > rhs); }
    friend constexpr bool operator>=(const Float& lhs, const Float& rhs) { return !(lhs < rhs); }
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

constexpr __CoreCpp::Int operator "" _i(unsigned long long v) { return __CoreCpp::Int(static_cast<int64_t>(v)); }
constexpr __CoreCpp::BigInt operator "" _I(const char* v) { return __CoreCpp::BigInt(v); }
constexpr __CoreCpp::Nat operator "" _n(unsigned long long v) { return __CoreCpp::Nat(static_cast<uint64_t>(v)); }
constexpr __CoreCpp::BigNat operator "" _N(const char* v) { return __CoreCpp::BigNat(v); }
constexpr __CoreCpp::Float operator "" _f(long double v) { return __CoreCpp::Float(static_cast<double>(v)); }
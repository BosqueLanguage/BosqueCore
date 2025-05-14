#pragma once

#include <stdint.h>
#include <iostream>
#include <cmath>

namespace __CoreCpp {

#define MAX_BSQ_INT ((int64_t(1) << 62) - 1)
#define MIN_BSQ_INT (-(int64_t(1) << 62)) 
#define MAX_BSQ_BIGINT ((__int128_t(1) << 126) - 1)
#define MIN_BSQ_BIGINT (-(__int128_t(1) << 126))
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
    constexpr Int() noexcept : value(0) {};
    constexpr explicit Int(int64_t val) : value(val){ 
        if(!is_valid_int(val)) {
            throw std::runtime_error("Invalid size for 63 bit signed integer!\n");
        }
    }; 

    // Overloaded operations on Int
    constexpr Int operator+(Int const& rhs) { 
        int64_t res = 0;
        if(__builtin_add_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit signed integers!\n");
        }

        return Int(res);
    }
    constexpr Int operator-(Int const& rhs) { 
        int64_t res = 0;
        if(__builtin_sub_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on subtraction of two 63 bit signed integers!\n");
        }
        return Int(res);
    }
    constexpr Int operator/(Int const& rhs) {
        int64_t res = 0;
        if(rhs.value == 0 || (value == MIN_BSQ_INT && rhs.value == -1)) {
            throw std::runtime_error("Overflow detected on division of two 63 bit signed integers!\n");
        }
        return Int(value / rhs.value);
    }
    constexpr Int operator*(Int const& rhs) {
        int64_t res = 0;
        if(__builtin_mul_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on multiplication of two 63 bit signed integers!\n");
        }
        return Int(res);
    }
    constexpr bool operator==(Int const& rhs) const { return value == rhs.value; }
    constexpr bool operator!=(Int const& rhs) const { return value != rhs.value; }
    constexpr bool operator<(Int const& rhs) const { return value < rhs.value; }
    constexpr bool operator<=(Int const& rhs) const { return value <= rhs.value; }
    constexpr bool operator>(Int const& rhs) const { return value > rhs.value; }
    constexpr bool operator>=(Int const& rhs) const { return value >= rhs.value; }
};

// Signed 127 bit value
class BigInt {
    __int128_t value;
    static constexpr __int128_t to_int128(const char* v) {
        __int128_t res = 0, neg = 0;        
        const char* p = v;

        // Check for sign
        if(*p == '-') {
            neg = 1;
            p++;
        }
        else if(*p == '+') {
            neg = 0;
            p++;
        }

        while(*p >= '0' && *p <= '9') {
            if(neg) {
                res = (res * 10) - (*p - '0');
            }
            else {
                res = (res * 10) + (*p - '0');
            }
            p++;
        }

        return res;
    }
public:
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
    constexpr BigInt operator+(BigInt const& rhs) { 
        __int128_t res = 0;
        if(__builtin_add_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit signed integers!\n");
        }

        return BigInt(res);
    }
    constexpr BigInt operator-(BigInt const& rhs) {
        __int128_t res = 0;
        if(__builtin_sub_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on subtraction of two 127 bit signed integers!\n");
        }

        return BigInt(res);
    }
    constexpr BigInt operator/(BigInt const& rhs) {
        __int128_t res = 0;
        if(rhs.value == 0 || (value == MIN_BSQ_BIGINT && rhs.value == -1)) {
            throw std::runtime_error("Overflow detected on division of two 127 bit signed integers!\n");
        }
        return BigInt(value / rhs.value);
    }
    constexpr BigInt operator*(BigInt const& rhs) {
        __int128_t res = 0;
        if(__builtin_mul_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on multiplication of two 127 bit signed integers!\n");
        }

        return BigInt(res);
    }
    constexpr bool operator==(BigInt const& rhs) const { return value == rhs.value; }
    constexpr bool operator!=(BigInt const& rhs) const { return value != rhs.value; }
    constexpr bool operator<(BigInt const& rhs) const { return value < rhs.value; }
    constexpr bool operator<=(BigInt const& rhs) const { return value <= rhs.value; }
    constexpr bool operator>(BigInt const& rhs) const { return value > rhs.value; }
    constexpr bool operator>=(BigInt const& rhs) const { return value >= rhs.value; }
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
    constexpr Nat operator+(Nat const& rhs) {
        uint64_t res = 0;
        if(__builtin_add_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on addition of two 63 bit unsigned integers!\n");
        }

        return Nat(res);
    }
    constexpr Nat operator-(Nat const& rhs) {
        uint64_t res = 0;
        if(__builtin_sub_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on subtraction of two 63 bit unsigned integers!\n");
        }

        return Nat(res);
    }
    constexpr Nat operator/(Nat const& rhs) {
        uint64_t res = 0;
        if(rhs.value == 0) {
            throw std::runtime_error("Overflow detected on division of two 63 bit unsigned integers!\n");
        }
        return Nat(value / rhs.value);
    }
    constexpr Nat operator*(Nat const& rhs) {
        uint64_t res = 0;
        if(__builtin_mul_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on multiplication of two 63 bit unsigned integers!\n");
        }

        return Nat(res);
    }
    constexpr bool operator==(Nat const& rhs) const { return value == rhs.value; }
    constexpr bool operator!=(Nat const& rhs) const { return value != rhs.value; }
    constexpr bool operator<(Nat const& rhs) const { return value < rhs.value; }
    constexpr bool operator<=(Nat const& rhs) const { return value <= rhs.value; }
    constexpr bool operator>(Nat const& rhs) const { return value > rhs.value; }
    constexpr bool operator>=(Nat const& rhs) const { return value >= rhs.value; }
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
    
    // Overloaded operators on BigNat
    constexpr BigNat operator+(BigNat const& rhs) {
        __uint128_t res = 0;
        if(__builtin_add_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on addition of two 127 bit unsigned integers!\n");
        } 
        
        return BigNat(res);
    }
    constexpr BigNat operator-(BigNat const& rhs) {
        __uint128_t res = 0;
        if(__builtin_sub_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on subtraction of two 127 bit unsigned integers!\n");
        }

        return BigNat(res);
    }
    constexpr BigNat operator/(BigNat const& rhs) {
        __uint128_t res = 0;
        if(rhs.value == 0) {
            throw std::runtime_error("Overflow detected on division of two 127 bit unsigned integers!\n");
        }
        return BigNat(value / rhs.value);
    }
    constexpr BigNat operator*(BigNat const& rhs) {
        __uint128_t res = 0;
        if(__builtin_mul_overflow(value, rhs.value, &res)) {
            throw std::runtime_error("Overflow detected on multiplication of two 127 bit unsigned integers!\n");
        }

        return BigNat(res);
    }
    constexpr bool operator==(BigNat const& rhs) const { return value == rhs.value; }
    constexpr bool operator!=(BigNat const& rhs) const { return value != rhs.value; }
    constexpr bool operator<(BigNat const& rhs) const { return value < rhs.value; }
    constexpr bool operator<=(BigNat const& rhs) const { return value <= rhs.value; }
    constexpr bool operator>(BigNat const& rhs) const { return value > rhs.value; }
    constexpr bool operator>=(BigNat const& rhs) const { return value >= rhs.value; }
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

    // Overloaded operators on float
    constexpr Float operator+(Float const& rhs) { return Float(value + rhs.value); }
    constexpr Float operator-(Float const& rhs) { return Float(value - rhs.value); }
    constexpr Float operator/(Float const& rhs) { return Float(value / rhs.value); }
    constexpr Float operator*(Float const& rhs) { return Float(value * rhs.value); }
    constexpr bool operator==(Float const& rhs) const { return value == rhs.value; }
    constexpr bool operator!=(Float const& rhs) const { return value != rhs.value; }
    constexpr bool operator<(Float const& rhs) const { return value < rhs.value; }
    constexpr bool operator<=(Float const& rhs) const { return value <= rhs.value; }
    constexpr bool operator>(Float const& rhs) const { return value > rhs.value; }
    constexpr bool operator>=(Float const& rhs) const { return value >= rhs.value; }
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
#pragma once

#include <stdint.h>
#include <iostream>

#define BIT_MASK (0x7FFFFFFFFFFFFFF)

namespace __CoreCpp {

// Signed 63 bit value
class Int {
    int64_t value;
    constexpr explicit Int(int64_t val) : value(val & BIT_MASK) {}; 
public:
    constexpr Int() noexcept : value(0) {};
    constexpr int64_t get() const noexcept { return value; }

    // We overload literal "_i" to easily match our types
    static constexpr Int from_literal(int64_t v) { return Int(v); }

    // TODO: Overload any operators in Int
};
constexpr Int operator"" _i(unsigned long long v);

// Unsigned 63 bit value
class Nat {
    uint64_t value;
    constexpr explicit Nat(uint64_t val) : value(val & BIT_MASK) {}; 
public:
    constexpr Nat() noexcept : value(0) {};
    constexpr int64_t get() const noexcept { return value; }

    // We overload literal "_i" to easily match our types
    static constexpr Nat from_literal(int64_t v) { return Nat(v); }

    // TODO: Overload any operators in Nat 
};
constexpr Nat operator"" _n(unsigned long long v);

//
// TODO: Figure out representation for BigNat, BigInt, Float
//

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

// We MAY want to define these in cppruntime.cpp, leaving here for now
// Overloading of numeric tags at global scope
constexpr __CoreCpp::Int operator"" _i(unsigned long long v) { return __CoreCpp::Int::from_literal(static_cast<int64_t>(v)); }
constexpr __CoreCpp::Nat operator"" _n(unsigned long long v) { return __CoreCpp::Nat::from_literal(static_cast<int64_t>(v)); }
#pragma once

#include <stdint.h>
#include <iostream>
#include <cmath>
#include <csetjmp>

namespace __CoreCpp {

#define MAX_BSQ_INT ((int64_t(1) << 62) - 1)
#define MIN_BSQ_INT (-(int64_t(1) << 62) + 1) 
#define MAX_BSQ_BIGINT ((__int128_t(1) << 126) - 1)
#define MIN_BSQ_BIGINT (-(__int128_t(1) << 126) + 1)
#define MAX_BSQ_NAT ((uint64_t(1) << 63) - 1)
#define MAX_BSQ_BIGNAT ((__uint128_t(1) << 127) - 1)

#define is_valid_Int(V) ((V >= MIN_BSQ_INT) && (V <= MAX_BSQ_INT))
#define is_valid_BigInt(V) ((V >= MIN_BSQ_BIGINT) && (V <= MAX_BSQ_BIGINT))
#define is_valid_Nat(V) (V <= MAX_BSQ_NAT)
#define is_valid_BigNat(V) (V <= MAX_BSQ_BIGNAT)

#define do_safe_arithmetic(BSQ_TYPE, VAL_TYPE, TYPE)                \
do {                                                                \
    VAL_TYPE tmp = 0;                                               \
    if(__builtin_##TYPE##_overflow(this->value, rhs.value, &tmp)) { \
        std::longjmp(info.error_handler, true);                     \
    }                                                               \
    if(!is_valid_##BSQ_TYPE(tmp)) {                                 \
        std::longjmp(info.error_handler, true);                     \
    }                                                               \
    this->value = tmp;                                              \
    return *this;                                                   \
}while(0)                                                           \

#define do_safe_division()                      \
do {                                            \
    if(rhs.value == 0) {                        \
        std::longjmp(info.error_handler, true); \
    }                                           \
    this->value /= rhs.value;                   \
    return *this;                               \
}while(0)                                       \

#define do_safe_float_arithmetic(OP)            \
do {                                            \
    double res = this->value OP rhs.value;      \
    if(!std::isfinite(res)) {                   \
        std::longjmp(info.error_handler, true); \
    }                                           \
    this->value = res;                          \
    return *this;                               \
} while(0)                                      \

class ThreadLocalInfo {
public:
    std::jmp_buf error_handler;

    ThreadLocalInfo() {} 
    static ThreadLocalInfo& get() {
        thread_local ThreadLocalInfo instance;
        return instance;
    }

    // Cannot copy or move thread local info
    ThreadLocalInfo(const ThreadLocalInfo&) = delete;
    ThreadLocalInfo& operator=(const ThreadLocalInfo&) = delete;
};
ThreadLocalInfo& info = ThreadLocalInfo::get();

//
// Converts string into corresponding integer representation. Used when
// converting our literals to 128 bit values.
//
template<typename T>
constexpr T string_to_t(const char* s) {
    T res = 0;  
    const char* p = s;

    while(*p >= '0' && *p <= '9') {
        res = (res * 10) + (*p - '0');
        p++;
    }

    return res;
}

// Signed 63 bit value
class Int {
    int64_t value;
public:
    constexpr Int() noexcept : value(0) {};
    constexpr explicit Int(int64_t val) noexcept : value(val){ 
        if(!is_valid_Int(val)) {
            std::longjmp(info.error_handler, true);
        }
    }; 

    // Overloaded operations on Int
    constexpr Int& operator+=(const Int& rhs) noexcept {
        do_safe_arithmetic(Int, int64_t, add);
    }
    constexpr Int& operator-=(const Int& rhs) noexcept {
        do_safe_arithmetic(Int, int64_t, sub);
    }
    constexpr Int& operator/=(const Int& rhs) noexcept {
        do_safe_division();
    }
    constexpr Int& operator*=(const Int& rhs) noexcept {
        do_safe_arithmetic(Int, int64_t, mul);
    }
    constexpr Int operator-() noexcept { // dont want to modify value here
        if(value == MIN_BSQ_INT) {
            std::longjmp(info.error_handler, true);
        }
        return Int(-value);
    }
    friend constexpr Int operator+(Int lhs, const Int& rhs) noexcept { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr Int operator-(Int lhs, const Int& rhs) noexcept { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr Int operator/(Int lhs, const Int& rhs) noexcept {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr Int operator*(Int lhs, const Int& rhs) noexcept {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const Int& lhs, const Int& rhs) noexcept { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const Int& lhs, const Int& rhs) noexcept { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const Int& lhs, const Int& rhs) noexcept { return rhs < lhs; }
    friend constexpr bool operator!=(const Int& lhs, const Int& rhs) noexcept { return !(lhs == rhs); }
    friend constexpr bool operator<=(const Int& lhs, const Int& rhs) noexcept { return !(lhs > rhs); }
    friend constexpr bool operator>=(const Int& lhs, const Int& rhs) noexcept { return !(lhs < rhs); }
};

// Signed 127 bit value
class BigInt {
    __int128_t value;
public:
    constexpr BigInt() noexcept : value(0) {};

    // Used when constructing from bosque code
    constexpr explicit BigInt(const char* val) noexcept : value(string_to_t<__int128_t>(val)) {
        if(!is_valid_BigInt(value)) {
            std::longjmp(info.error_handler, true);
        }
    };

    // Used for negation
    constexpr explicit BigInt(__int128_t val) noexcept : value(val) {
        if(!is_valid_BigInt(val)) {
            std::longjmp(info.error_handler, true);
        }
    }; 

    // Overloaded operators on BigInt
    constexpr BigInt& operator+=(const BigInt& rhs) noexcept {
        do_safe_arithmetic(BigInt, __int128_t, add);
    }
    constexpr BigInt& operator-=(const BigInt& rhs) noexcept {
         do_safe_arithmetic(BigInt, __int128_t, sub);
    }
    constexpr BigInt& operator/=(const BigInt& rhs) noexcept { 
        do_safe_division();
    }
    constexpr BigInt& operator*=(const BigInt& rhs) noexcept {
        do_safe_arithmetic(BigInt, __int128_t, mul);
    }
    constexpr BigInt operator-() noexcept { // dont want to modify value here
        if(this->value == MIN_BSQ_BIGINT) {
            std::longjmp(info.error_handler, true);
        }
        return BigInt(-value);
    }
    friend constexpr BigInt operator+(BigInt lhs, const BigInt& rhs) noexcept { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr BigInt operator-(BigInt lhs, const BigInt& rhs) noexcept { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr BigInt operator/(BigInt lhs, const BigInt& rhs) noexcept {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr BigInt operator*(BigInt lhs, const BigInt& rhs) noexcept {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const BigInt& lhs, const BigInt& rhs) noexcept { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const BigInt& lhs, const BigInt& rhs) noexcept { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const BigInt& lhs, const BigInt& rhs) noexcept { return rhs < lhs; }
    friend constexpr bool operator!=(const BigInt& lhs, const BigInt& rhs) noexcept { return !(lhs == rhs); }
    friend constexpr bool operator<=(const BigInt& lhs, const BigInt& rhs) noexcept { return !(lhs > rhs); }
    friend constexpr bool operator>=(const BigInt& lhs, const BigInt& rhs) noexcept { return !(lhs < rhs); } 
};

// Unsigned 63 bit value
class Nat {
    uint64_t value;
public:
    constexpr Nat() noexcept : value(0) {};
    constexpr explicit Nat(uint64_t val) noexcept : value(val) {
        if(!is_valid_Nat(val)) {
            std::longjmp(info.error_handler, true);
        }
    }; 

    // Overloaded operators on Nat
    constexpr Nat& operator+=(const Nat& rhs) noexcept {
        do_safe_arithmetic(Nat, uint64_t, add);
    }
    constexpr Nat& operator-=(const Nat& rhs) noexcept {
        do_safe_arithmetic(Nat, uint64_t, sub);
    }
    constexpr Nat& operator/=(const Nat& rhs) noexcept {
        do_safe_division();
    }
    constexpr Nat& operator*=(const Nat& rhs) noexcept {
        do_safe_arithmetic(Nat, uint64_t, mul);
    }
    friend constexpr Nat operator+(Nat lhs, const Nat& rhs) noexcept { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr Nat operator-(Nat lhs, const Nat& rhs) noexcept { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr Nat operator/(Nat lhs, const Nat& rhs) noexcept {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr Nat operator*(Nat lhs, const Nat& rhs) noexcept {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const Nat& lhs, const Nat& rhs) noexcept { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const Nat& lhs, const Nat& rhs) noexcept { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const Nat& lhs, const Nat& rhs) noexcept { return rhs < lhs; }
    friend constexpr bool operator!=(const Nat& lhs, const Nat& rhs) noexcept { return !(lhs == rhs); }
    friend constexpr bool operator<=(const Nat& lhs, const Nat& rhs) noexcept { return !(lhs > rhs); }
    friend constexpr bool operator>=(const Nat& lhs, const Nat& rhs) noexcept { return !(lhs < rhs); } 
};

// Unsigned 127 bit value
class BigNat {
    __uint128_t value;
public:
    constexpr BigNat() noexcept : value(0) {};

    // Used when constructing from bosque code
    constexpr explicit BigNat(const char* val) noexcept : value(string_to_t<__uint128_t>(val)) {
        if(!is_valid_BigNat(value)) {
            std::longjmp(info.error_handler, true);
        }
    }; 

    // Used with negation 
    constexpr explicit BigNat(__uint128_t val) noexcept : value(val) {
        if(!is_valid_BigNat(val)) {
            std::longjmp(info.error_handler, true);
        }
    };
    
    // Overloaded operators on BigInt
    constexpr BigNat& operator+=(const BigNat& rhs) noexcept {
        do_safe_arithmetic(BigNat, __uint128_t, add);
    }
    constexpr BigNat& operator-=(const BigNat& rhs) noexcept {
        do_safe_arithmetic(BigNat, __uint128_t, sub);
    }
    constexpr BigNat& operator/=(const BigNat& rhs) noexcept {
        do_safe_division();
    }
    constexpr BigNat& operator*=(const BigNat& rhs) noexcept {
        do_safe_arithmetic(BigNat, __uint128_t, mul);
    }
    friend constexpr BigNat operator+(BigNat lhs, const BigNat& rhs) noexcept { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr BigNat operator-(BigNat lhs, const BigNat& rhs) noexcept { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr BigNat operator/(BigNat lhs, const BigNat& rhs) noexcept {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr BigNat operator*(BigNat lhs, const BigNat& rhs) noexcept {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const BigNat& lhs, const BigNat& rhs) noexcept { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const BigNat& lhs, const BigNat& rhs) noexcept { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const BigNat& lhs, const BigNat& rhs) noexcept { return rhs < lhs; }
    friend constexpr bool operator!=(const BigNat& lhs, const BigNat& rhs) noexcept { return !(lhs == rhs); }
    friend constexpr bool operator<=(const BigNat& lhs, const BigNat& rhs) noexcept { return !(lhs > rhs); }
    friend constexpr bool operator>=(const BigNat& lhs, const BigNat& rhs) noexcept { return !(lhs < rhs); }
};

// 64 bit base 2 floats
class Float {
    double value;
public:
    constexpr Float() noexcept : value(0) {};
     constexpr explicit Float(double val) noexcept : value(val) { 
        if(!std::isfinite(val)) { 
            std::longjmp(info.error_handler, true);
        } 
    }

    static constexpr Float from_literal(double v) noexcept { return Float(v); }

    // Overloaded operations on Float
    constexpr Float& operator+=(const Float& rhs) noexcept {
        do_safe_float_arithmetic(+); 
    }
    constexpr Float& operator-=(const Float& rhs) noexcept {
        do_safe_float_arithmetic(-);
    }
    constexpr Float& operator/=(const Float& rhs) noexcept { 
        do_safe_float_arithmetic(/);
    }
    constexpr Float& operator*=(const Float& rhs) noexcept {
        do_safe_float_arithmetic(*);
    }
    constexpr Float operator-() noexcept { // dont want to modify value here
        return Float(-this->value);
    }
    friend constexpr Float operator+(Float lhs, const Float& rhs) noexcept { 
        lhs += rhs;
        return lhs;
    }
    friend constexpr Float operator-(Float lhs, const Float& rhs) noexcept { 
        lhs -= rhs;
        return lhs;
    }
    friend constexpr Float operator/(Float lhs, const Float& rhs) noexcept {
        lhs /= rhs;
        return lhs;
    }
    friend constexpr Float operator*(Float lhs, const Float& rhs) noexcept {
        lhs *= rhs;
        return lhs;
    }
    friend constexpr bool operator<(const Float& lhs, const Float& rhs) noexcept { return lhs.value < rhs.value; }
    friend constexpr bool operator==(const Float& lhs, const Float& rhs) noexcept { return lhs.value == rhs.value; }
    friend constexpr bool operator>(const Float& lhs, const Float& rhs) noexcept { return rhs < lhs; }
    friend constexpr bool operator!=(const Float& lhs, const Float& rhs) noexcept { return !(lhs == rhs); }
    friend constexpr bool operator<=(const Float& lhs, const Float& rhs) noexcept { return !(lhs > rhs); }
    friend constexpr bool operator>=(const Float& lhs, const Float& rhs) noexcept { return !(lhs < rhs); }
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
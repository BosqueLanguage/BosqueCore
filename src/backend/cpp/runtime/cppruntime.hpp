#pragma once

#include <stdint.h>
#include <iostream>
#include <cmath>
#include <csetjmp>
#include <variant> // TODO: Need to remove dependency!

namespace __CoreCpp {

// Note: This will be deleted when the GC is merged, only exists so emitted cpp still compiles
struct FieldOffsetInfo 
{
    uint16_t id;
    uint16_t type;
    uint32_t byteoffset;
};

struct TypeInfoBase 
{
    uint32_t type_id;
    uint32_t type_size;
    uint32_t slot_size;
    const char* ptr_mask;
    const char* typekey;
    const FieldOffsetInfo* vtable; // Will need to add to gc
};

template <size_t N>
inline void memcpy(uintptr_t* dst, const uintptr_t* src) noexcept {
    for(size_t i = 0; i < N; i++) {
        dst[i] = src[i];
    }
}

template <size_t K>
class Boxed {
public:
    TypeInfoBase* typeinfo = nullptr;
    uintptr_t data[K] = {};

    Boxed() noexcept = default;
    Boxed(const Boxed& rhs) noexcept : typeinfo(rhs.typeinfo) {
        memcpy<K>(this->data, rhs.data);
    }
    Boxed& operator=(const Boxed& rhs) noexcept {
        if(this != &rhs) {
            this->typeinfo = rhs.typeinfo;
            memcpy<K>(this->data, rhs.data);
        }
        return *this;
    }

    // Some constructor
    Boxed(TypeInfoBase* ti, uintptr_t d[K]) noexcept : typeinfo(ti) {
        memcpy<K>(this->data, d);
    }

    // None constructor
    Boxed(TypeInfoBase* ti) noexcept : typeinfo(ti) {}
};

template<>
class Boxed<1> {
public:
    TypeInfoBase* typeinfo = nullptr;
    uintptr_t data = 0;

    Boxed() noexcept = default;
    Boxed(const Boxed& rhs) noexcept : typeinfo(rhs.typeinfo), data(rhs.data) {};
    Boxed& operator=(const Boxed& rhs) noexcept { 
        this->typeinfo = rhs.typeinfo;
        this->data = rhs.data;
        return *this;
    }

    // Some constructor
    Boxed(TypeInfoBase* ti, uintptr_t d) noexcept : typeinfo(ti), data(d) {};

    // None constructor
    Boxed(TypeInfoBase* ti) noexcept : typeinfo(ti) {};
};

template<>
class Boxed<0> {
public:
    TypeInfoBase* typeinfo = nullptr;

    Boxed() noexcept = default;
    Boxed(const Boxed& rhs) noexcept : typeinfo(rhs.typeinfo) {};
    Boxed& operator=(const Boxed& rhs) noexcept {
        this->typeinfo = rhs.typeinfo;
        return *this;
    }

    Boxed(TypeInfoBase* ti) noexcept: typeinfo(ti) {};
};

template <size_t K>
class TupleEntry {
public:
    uintptr_t data[K] = {};

    TupleEntry() noexcept = default;
    TupleEntry(const TupleEntry& rhs) noexcept {
        memcpy<K>(this->data, rhs->data);
    }
    TupleEntry& operator=(const TupleEntry& rhs) noexcept {
        memcpy<K>(this->data, rhs->data);
        
        return *this;
    }

    TupleEntry(uintptr_t* d) {
        memcpy<K>(this->data, d);
    }
};

template <>
class TupleEntry<1> {
public:
    uintptr_t data = 0;

    TupleEntry() noexcept = default;
    TupleEntry(const TupleEntry& rhs) noexcept : data(rhs.data) { }
    TupleEntry& operator=(const TupleEntry& rhs) noexcept {        
        data = rhs.data;
        return *this;
    }

    TupleEntry(uintptr_t* d) noexcept : data(*d) { }
};

// Tuple implementation
template <size_t K1, size_t K2>
class Tuple2 {
public:
    TupleEntry<K1> e1;
    TupleEntry<K2> e2;
    
    Tuple2() noexcept = default;
    Tuple2(const Tuple2& rhs) noexcept : e1(rhs.e1), e2(rhs.e2) { }
    Tuple2& operator=(const Tuple2& rhs) noexcept {
        e1 = rhs.e1;
        e2 = rhs.e2;

        return *this;
    }

    Tuple2(uintptr_t* d1, uintptr_t* d2) noexcept : e1(d1), e2(d2) { }
};

typedef uint64_t None;

#define MAX_BSQ_INT ((int64_t(1) << 62) - 1)
#define MIN_BSQ_INT (-(int64_t(1) << 62) + 1) 
#define MAX_BSQ_BIGINT ((__int128_t(1) << 126) - 1)
#define MIN_BSQ_BIGINT (-(__int128_t(1) << 126) + 1)
#define MAX_BSQ_NAT ((uint64_t(1) << 62) - 1)
#define MAX_BSQ_BIGNAT ((__uint128_t(1) << 126) - 1)

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
    constexpr int64_t get() const noexcept { return value; } 

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
    constexpr Int& operator+() noexcept {
        return *this;
    }
    constexpr Int operator-() noexcept { // dont want to modify value here
        if(this->value == MIN_BSQ_INT) {
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
    constexpr __int128_t get() const noexcept { return value; }

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
    constexpr BigInt& operator+() noexcept {
        return *this;
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
    constexpr uint64_t get() const noexcept { return value; } 

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
    constexpr Nat& operator+() noexcept {
        return *this;
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
    constexpr __uint128_t get() const noexcept { return value; }
    
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
    constexpr BigNat& operator+() noexcept {
        return *this;
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
    constexpr double get() const noexcept { return value; }

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
    constexpr Float& operator+() noexcept {
        return *this;
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

//
// Allows us to print 128 bit values
//
template<typename T>
constexpr std::string t_to_string(T v) {
    if(v == 0) {
        return "0";
    }

    std::string tmp, res;
    if(v < 0) {
        res.push_back('-');
        v = -v;
    }
    while (v > 0) {
        tmp.push_back((v % 10) + '0');
        v /= 10;
    }
    for(auto it = tmp.rbegin(); it != tmp.rend(); it++) {
        res.push_back(*it);
    }

    return res;
}

// Will need to support Bosque CString and String eventually
typedef std::variant<Int, Nat, BigInt, BigNat, Float, bool> MainType; 

//
// Converts return type of main to string
//
std::string to_string(MainType v) {
    if(std::holds_alternative<bool>(v)) {
        bool res = std::get<bool>(v);
        if(!res) {
            return "false";
        }
        return "true";
    }
    else if(std::holds_alternative<Int>(v)) {
        return std::to_string(std::get<Int>(v).get()) + "_i";
    }
    else if (std::holds_alternative<Nat>(v)) {
        return std::to_string(std::get<Nat>(v).get()) + "_n";
    }
    else if (std::holds_alternative<Float>(v)) {
        return std::to_string(std::get<Float>(v).get()) + "_f";
    }
    else if(std::holds_alternative<BigInt>(v)) {
        __int128_t res = std::get<BigInt>(v).get();
        return t_to_string<__int128_t>(res) + "_I";
    }
    else if(std::holds_alternative<BigNat>(v)) {
        __int128_t res = std::get<BigNat>(v).get();
        return t_to_string<__uint128_t>(res) + "_N";
    }
    else {
        return "Unable to print main return type!\n";
    }
}

} // namespace __CoreCpp

constexpr __CoreCpp::Int operator "" _i(unsigned long long v) { return __CoreCpp::Int(static_cast<int64_t>(v)); }
constexpr __CoreCpp::BigInt operator "" _I(const char* v) { return __CoreCpp::BigInt(v); }
constexpr __CoreCpp::Nat operator "" _n(unsigned long long v) { return __CoreCpp::Nat(static_cast<uint64_t>(v)); }
constexpr __CoreCpp::BigNat operator "" _N(const char* v) { return __CoreCpp::BigNat(v); }
constexpr __CoreCpp::Float operator "" _f(long double v) { return __CoreCpp::Float(static_cast<double>(v)); }

// For debugging
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Int& t) { return os << t.get(); }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigInt& t) { return os << __CoreCpp::t_to_string<__int128_t>(t.get()); }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Nat& t) { return os << t.get(); }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigNat& t) { return os << __CoreCpp::t_to_string<__uint128_t>(t.get()); }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Float& t) { return os << t.get(); }
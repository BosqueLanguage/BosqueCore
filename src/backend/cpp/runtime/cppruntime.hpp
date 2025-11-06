#pragma once

#include "gc/src/language/bsqtype.h"

#include <stdint.h>
#include <iostream>
#include <cmath>
#include <csetjmp>
#include <variant> // TODO: Need to remove dependency!

#define 𝐚𝐛𝐨𝐫𝐭 (std::longjmp(__CoreCpp::info.error_handler, true))
#define 𝐚𝐬𝐬𝐞𝐫𝐭(E) (void)((E) || (𝐚𝐛𝐨𝐫𝐭, 0))
#define 𝐫𝐞𝐪𝐮𝐢𝐫𝐞𝐬(𝐄) 𝐚𝐬𝐬𝐞𝐫𝐭(𝐄)
#define 𝐞𝐧𝐬𝐮𝐫𝐞𝐬(𝐄) 𝐚𝐬𝐬𝐞𝐫𝐭(𝐄)

#define 𝐰𝐡𝐢𝐥𝐞(s, guard, op) [&]() { auto state = s; while(guard(state)) { state = op(state); } return state; }()

namespace __CoreCpp {

typedef uintptr_t None;
typedef bool Bool;
typedef uint8_t CChar;
typedef uint32_t UnicodeChar;

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
extern ThreadLocalInfo& info;

template <size_t N>
inline void __attribute__((no_sanitize_address)) 
memcpy(uintptr_t* dst, const uintptr_t* src) noexcept {
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wstringop-overread"
    #pragma GCC diagnostic ignored "-Warray-bounds"
    for(size_t i = 0; i < N; i++) {
        dst[i] = src[i];
    }
    #pragma GCC diagnostic pop
}

template <size_t K>
class Boxed {
public:
    __CoreGC::TypeInfoBase* typeinfo = nullptr;
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

    template<typename T>
    Boxed(__CoreGC::TypeInfoBase* ti, T&& d) noexcept : typeinfo(ti) {
        static_assert(sizeof(T) <= K * sizeof(uintptr_t), "Object too large for Boxed<K>");
        memcpy<K>(this->data, reinterpret_cast<uintptr_t*>(&d));
    };

    // None constructor
    Boxed(__CoreGC::TypeInfoBase* ti) noexcept : typeinfo(ti) {}

    template<typename T, uintptr_t I=0>
    constexpr T access() noexcept { 
        return *reinterpret_cast<T*>(&this->data[I]);
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
    constexpr T access() noexcept { 
        return *reinterpret_cast<T*>(&this->data);
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

template <size_t K>
class TupleEntry {
public:
    uintptr_t data[K] = {};

    TupleEntry() noexcept = default;
    TupleEntry(const TupleEntry& rhs) noexcept {
        memcpy<K>(this->data, rhs.data);
    }
    TupleEntry& operator=(const TupleEntry& rhs) noexcept {
        memcpy<K>(this->data, rhs.data);
        
        return *this;
    }

    TupleEntry(uintptr_t* d) {
        memcpy<K>(this->data, d);
    }
};

// We may want to specialize K=2,3,4 as well
template <>
class TupleEntry<1> {
public:
    uintptr_t data = 0;

    TupleEntry() noexcept = default;
    TupleEntry(const TupleEntry& rhs) noexcept = default;
    TupleEntry& operator=(const TupleEntry& rhs) noexcept = default; 

    TupleEntry(uintptr_t* d) noexcept : data(*d) { }
};

template <size_t K0, size_t K1>
class Tuple2 {
public:
    TupleEntry<K0> e0 {};
    TupleEntry<K1> e1 {};
    
    Tuple2() noexcept = default;
    Tuple2(const Tuple2& rhs) noexcept = default; 
    Tuple2& operator=(const Tuple2& rhs) noexcept = default;

    template<typename T0, typename T1>
    Tuple2(T0&& d0, T1&& d1) noexcept 
        : e0(reinterpret_cast<uintptr_t*>(&d0)), e1(reinterpret_cast<uintptr_t*>(&d1)) {
            static_assert(sizeof(T0) <= K0 * sizeof(uintptr_t), "Object T0 too large for Tuple");
            static_assert(sizeof(T1) <= K1 * sizeof(uintptr_t), "Object T1 too large for Tuple");
        }

    template<typename T, size_t I>
    constexpr T access() noexcept {
        static_assert(I >= 0 && I <= 1);
        switch(I) {
            case 0: return *reinterpret_cast<T*>(&this->e0); break;
            case 1: return *reinterpret_cast<T*>(&this->e1); break;
        }
    }
};

template <size_t K0, size_t K1, size_t K2>
class Tuple3 {
public:
    TupleEntry<K0> e0 {};
    TupleEntry<K1> e1 {};
    TupleEntry<K2> e2 {};
    
    Tuple3() noexcept = default;
    Tuple3(const Tuple3& rhs) noexcept = default;
    Tuple3& operator=(const Tuple3& rhs) noexcept = default;

    template<typename T0, typename T1, typename T2>
    Tuple3(T0&& d0, T1&& d1, T2&& d2) noexcept 
        : e0(reinterpret_cast<uintptr_t*>(&d0)), e1(reinterpret_cast<uintptr_t*>(&d1)),
          e2(reinterpret_cast<uintptr_t*>(&d2)) {
            static_assert(sizeof(T0) <= K0 * sizeof(uintptr_t), "Object T0 too large for Tuple");
            static_assert(sizeof(T1) <= K1 * sizeof(uintptr_t), "Object T1 too large for Tuple");
            static_assert(sizeof(T2) <= K2 * sizeof(uintptr_t), "Object T2 too large for Tuple");
        }

    template<typename T, size_t I>
    constexpr T access() noexcept {
        static_assert(I >= 0 && I <= 2); 
        switch(I) {
            case 0: return *reinterpret_cast<T*>(&this->e0); break;
            case 1: return *reinterpret_cast<T*>(&this->e1); break;
            case 2: return *reinterpret_cast<T*>(&this->e2); break;
        }
    }
};

template <size_t K0, size_t K1, size_t K2, size_t K3>
class Tuple4 {
public:
    TupleEntry<K0> e0 {};
    TupleEntry<K1> e1 {};
    TupleEntry<K2> e2 {};
    TupleEntry<K3> e3 {};
    
    Tuple4() noexcept = default;
    Tuple4(const Tuple4& rhs) noexcept = default; 
    Tuple4& operator=(const Tuple4& rhs) noexcept = default;

    template<typename T0, typename T1, typename T2, typename T3>
    Tuple4(T0&& d0, T1&& d1, T2&& d2, T3&& d3) noexcept 
        : e0(reinterpret_cast<uintptr_t*>(&d0)), e1(reinterpret_cast<uintptr_t*>(&d1)),
          e2(reinterpret_cast<uintptr_t*>(&d2)), e3(reinterpret_cast<uintptr_t*>(&d3)) {
            static_assert(sizeof(T0) <= K0 * sizeof(uintptr_t), "Object T0 too large for Tuple");
            static_assert(sizeof(T1) <= K1 * sizeof(uintptr_t), "Object T1 too large for Tuple");
            static_assert(sizeof(T2) <= K2 * sizeof(uintptr_t), "Object T2 too large for Tuple");
            static_assert(sizeof(T3) <= K3 * sizeof(uintptr_t), "Object T3 too large for Tuple");
        }

    template<typename T, size_t I>
    constexpr T access() noexcept {
        static_assert(I >= 0 && I <= 3);  
        switch(I) {
            case 0: return *reinterpret_cast<T*>(&this->e0); break;
            case 1: return *reinterpret_cast<T*>(&this->e1); break;
            case 2: return *reinterpret_cast<T*>(&this->e2); break;
            case 3: return *reinterpret_cast<T*>(&this->e3); break;
        }
    }
};

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
        𝐚𝐛𝐨𝐫𝐭;                                                       \
    }                                                               \
    if(!is_valid_##BSQ_TYPE(tmp)) {                                 \
        𝐚𝐛𝐨𝐫𝐭;                                                       \
    }                                                               \
    this->value = tmp;                                              \
    return *this;                                                   \
}while(0)                                                           \

#define do_safe_division()                      \
do {                                            \
    if(rhs.value == 0) {                        \
        𝐚𝐛𝐨𝐫𝐭;                                   \
    }                                           \
    this->value /= rhs.value;                   \
    return *this;                               \
}while(0)                                       \

#define do_safe_float_arithmetic(OP)            \
do {                                            \
    double res = this->value OP rhs.value;      \
    if(!std::isfinite(res)) {                   \
        𝐚𝐛𝐨𝐫𝐭;                                   \
    }                                           \
    this->value = res;                          \
    return *this;                               \
} while(0)                                      \

// Signed 63 bit value
class Int {
    int64_t value;
public:
    constexpr Int() noexcept : value(0) {};
    constexpr explicit Int(int64_t val) noexcept : value(val){ 
        if(!is_valid_Int(val)) {
            𝐚𝐛𝐨𝐫𝐭;
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
            𝐚𝐛𝐨𝐫𝐭;
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

template<uint64_t NBits>
struct PackedBits {
    static constexpr uint64_t WORDS_NEEDED = (NBits + 63) / 64;
    uint64_t data[WORDS_NEEDED] = { 0 };
    
    constexpr void set(uint64_t index) noexcept {
        uint64_t word = index / 64;
        uint64_t bit = index % 64;
        this->data[word] |= (1ULL << bit);
     }
    
    Bool get(uint64_t index) const noexcept {
        uint64_t word = index / 64;
        uint64_t bit = index % 64;
        return (this->data[word] >> bit) & 1;
    }
};

template<uint64_t NTypes>
class SubtypeTable {
private:
    PackedBits<NTypes * NTypes> bits;
    
    // type id of 0 is reserved
    static constexpr uint64_t getTypeOffset(uint64_t super, uint64_t sub) noexcept {
        return (super - 1) * NTypes + (sub - 1);
    }

public:
    constexpr SubtypeTable() noexcept : bits() {};

    template<uint64_t super, uint64_t... subs>
    constexpr void set() noexcept {
        𝐚𝐬𝐬𝐞𝐫𝐭(super >= 1 && super <= NTypes);
        ((𝐚𝐬𝐬𝐞𝐫𝐭(subs >= 1 && subs <= NTypes)), ...);
        
        this->bits.set(getTypeOffset(super, super));
        (this->bits.set(getTypeOffset(super, subs)), ...);
    }
    
    inline Bool get(uint64_t super, uint64_t sub) const noexcept {
        𝐚𝐬𝐬𝐞𝐫𝐭(sub >= 1 && sub <= NTypes);
        𝐚𝐬𝐬𝐞𝐫𝐭(super >= 1 && super <= NTypes);
       
        return this->bits.get(getTypeOffset(super, sub));
    }
};

//
// Converts string into corresponding integer representation. Used when
// converting our literals to 128 bit values.
//
template<typename T>
constexpr T string_to_t(const char* s) noexcept {
    T res = 0;  
    const char* p = s;

    while(*p >= '0' && *p <= '9') {
        res = (res * 10) + (*p - '0');
        p++;
    }

    return res;
}

//
// Allows us to print 128 bit values
//
template<typename T>
constexpr std::string t_to_string(T v) noexcept {
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

// Signed 127 bit value
class BigInt {
    __int128_t value;
public:
    constexpr BigInt() noexcept : value(0) {};

    // Used when constructing from bosque code
    constexpr explicit BigInt(const char* val) noexcept : value(string_to_t<__int128_t>(val)) {
        if(!is_valid_BigInt(value)) {
            𝐚𝐛𝐨𝐫𝐭;
        }
    };

    // Used for negation
    constexpr explicit BigInt(__int128_t val) noexcept : value(val) {
        if(!is_valid_BigInt(val)) {
            𝐚𝐛𝐨𝐫𝐭;
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
            𝐚𝐛𝐨𝐫𝐭;
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
            𝐚𝐛𝐨𝐫𝐭;
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
            𝐚𝐛𝐨𝐫𝐭;
        }
    }; 

    // Used with negation 
    constexpr explicit BigNat(__uint128_t val) noexcept : value(val) {
        if(!is_valid_BigNat(val)) {
            𝐚𝐛𝐨𝐫𝐭;
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
            𝐚𝐛𝐨𝐫𝐭;
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

// We say for now no more than 8 chars, may want to make this dynamically pick 8 or 16 max
const int maxCCharBufferSize = 8;
struct CCharBuffer {
    CChar chars[maxCCharBufferSize] {};
    Nat size {0};

    static CCharBuffer create_empty();
    static CCharBuffer create_1(CChar c1);
    static CCharBuffer create_2(CChar c1, CChar c2);
    static CCharBuffer create_3(CChar c1, CChar c2, CChar c3);
    static CCharBuffer create_4(CChar c1, CChar c2, CChar c3, CChar c4);
    static CCharBuffer create_5(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5);
    static CCharBuffer create_6(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6);
    static CCharBuffer create_7(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6, CChar c7);
    static CCharBuffer create_8(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6, CChar c7, CChar c8);
};

CCharBuffer cbufferFromStringLiteral(size_t ptr, size_t size, const CChar* &basestr) noexcept;
CCharBuffer cbufferFromNat(Nat v) noexcept;
CCharBuffer& cbufferMerge(CCharBuffer& cb1, CCharBuffer& cb2) noexcept;
CCharBuffer& cbufferRemainder(CCharBuffer& cb, Nat split) noexcept;
Bool cbufferEqual(CCharBuffer& cb1, CCharBuffer& cb2) noexcept;
Bool cbufferLess(CCharBuffer& cb1, CCharBuffer& cb2) noexcept;
Bool cbufferIsPrefix(CCharBuffer cb, CCharBuffer& pre) noexcept;
CCharBuffer& cbufferRemove(CCharBuffer& cb1, CCharBuffer& pre) noexcept;

const int maxUnicodeCharBufferSize = 8;
struct UnicodeCharBuffer {
    UnicodeChar chars[8] {};
    Nat size {0};

    static UnicodeCharBuffer create_empty();
    static UnicodeCharBuffer create_1(UnicodeChar c1);
    static UnicodeCharBuffer create_2(UnicodeChar c1, UnicodeChar c2);
    static UnicodeCharBuffer create_3(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3);
    static UnicodeCharBuffer create_4(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4);
    static UnicodeCharBuffer create_5(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5);
    static UnicodeCharBuffer create_6(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6);
    static UnicodeCharBuffer create_7(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6, UnicodeChar c7);
    static UnicodeCharBuffer create_8(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6, UnicodeChar c7, UnicodeChar c8);
};

UnicodeCharBuffer ubufferFromStringLiteral(size_t ptr, size_t size, const UnicodeChar* &basestr) noexcept;
UnicodeCharBuffer& ubufferMerge(UnicodeCharBuffer& ub1, UnicodeCharBuffer& ub2) noexcept;
UnicodeCharBuffer& ubufferRemainder(UnicodeCharBuffer& ub, Nat split) noexcept;

inline Bool ubuf_memcmp(UnicodeChar b1[maxUnicodeCharBufferSize], UnicodeChar b2[maxUnicodeCharBufferSize]) noexcept {
    static_assert(sizeof(uintptr_t) == 2 * sizeof(UnicodeChar));
    static_assert(maxUnicodeCharBufferSize % (sizeof(uintptr_t) / sizeof(UnicodeChar)) == 0);

    UnicodeChar* cur_b1 = b1;
    UnicodeChar* cur_b2 = b2;

    constexpr size_t chars_per_chunk = sizeof(uintptr_t) / sizeof(UnicodeChar);
    constexpr size_t num_chunks = maxUnicodeCharBufferSize / chars_per_chunk;
    
    for (size_t i = 0; i < num_chunks; i++) {
        if (*reinterpret_cast<const uintptr_t*>(cur_b1) != *reinterpret_cast<const uintptr_t*>(cur_b2)) {
            return false;
        }
        cur_b1 += chars_per_chunk;
        cur_b2 += chars_per_chunk;
    }

    return true;
}

inline Bool ubufferEqual(UnicodeCharBuffer& ub1, UnicodeCharBuffer& ub2) noexcept {
    return ubuf_memcmp(ub1.chars, ub2.chars);
}

// Since nodes are always ref the size of a rope is dependant 
// on the buffers size, so this can be safely computed
typedef Boxed<sizeof(CCharBuffer) / 8> __CRope;
typedef Boxed<sizeof(UnicodeCharBuffer) / 8> __UnicodeRope;

struct __CRopeNode {
    uint64_t color;
    uint64_t weight;
    __CRope left;
    __CRope right;
};

struct __UnicodeRopeNode {
    uint64_t color;
    uint64_t weight;
    __UnicodeRope left;
    __UnicodeRope right;
};

// Path we have taken during tree walking
class Path {
    uint64_t pathBits;

    static const uint64_t PATH_LEFT = 1ull;
    static const uint64_t LSB_MASK  = 0x1ull; 
    
public:
    Path() : pathBits(0) {}

    inline bool isleft() const noexcept {
        return (pathBits & LSB_MASK) == PATH_LEFT;
    }

    // Going left pushes a 1
    inline void left() noexcept {
        this->pathBits <<= 1;
        this->pathBits |= PATH_LEFT;
    }

    // Going right pushes a 0
    inline void right() noexcept {
        this->pathBits <<= 1;
    }

    inline void up() noexcept {
        this->pathBits >>= 1;
    }
};

template<typename Rope>
class PathStack {
    Rope* stack[64];
    size_t index;

    Path path;
    bool wasLeftDirection;

    inline void storeLastDirection() noexcept {
        this->wasLeftDirection = this->path.isleft();
    }
public:
    PathStack() : stack(), index(0), path(), wasLeftDirection(false) {};

    inline bool empty() const noexcept {
        return index == 0;
    }
    
    inline bool wasLeft() noexcept {
        return this->wasLeftDirection;
    }

    inline void push(Rope& r) noexcept {
        this->stack[this->index++] = &r;
    }

    inline void left(Rope& r) noexcept {
        this->storeLastDirection();
        this->push(r);
        this->path.left();
    }

    inline void right(Rope& r) noexcept {
        this->storeLastDirection();
        this->push(r);
        this->path.right();
    }

    inline Rope& pop() noexcept {
        this->storeLastDirection();
        this->path.up();
            
        return *this->stack[--this->index];
    }

    inline Rope& top() const noexcept {
        return *this->stack[this->index - 1];
    }
};

class CRopeIterator {
    PathStack<__CRope> traversalStack;
    
    __CRope inlineString;
    bool isInline;

    // We will eventually want to compute these via ptr mask in constructor
    static const size_t LEFT_CHILD_OFFSET = 2;
    static const size_t RIGHT_CHILD_OFFSET = LEFT_CHILD_OFFSET + 3;

    void initializeTraversal(__CRope& root) noexcept;

    inline bool isAtLeaf() const noexcept {
        return this->traversalStack.top().typeinfo->tag == __CoreGC::Tag::Value;
    }

    void traverseLeft() noexcept;
    void traverseRight() noexcept;
public:    
    CRopeIterator(__CRope& root) noexcept : traversalStack(), inlineString(), isInline(false) {
        this->initializeTraversal(root);
    };

    CCharBuffer next() noexcept;

    inline bool hasNext() noexcept {
        return !this->traversalStack.empty() || this->isInline;
    }
};

class UnicodeRopeIterator {
    PathStack<__UnicodeRope> traversalStack;
    
    __UnicodeRope inlineString;
    bool isInline;

    // We will eventually want to compute these via ptr mask in constructor
    static const size_t LEFT_CHILD_OFFSET = 2;
    static const size_t RIGHT_CHILD_OFFSET = LEFT_CHILD_OFFSET + 6;

    void initializeTraversal(__UnicodeRope& root) noexcept;

    inline bool isAtLeaf() const noexcept {
        return this->traversalStack.top().typeinfo->tag == __CoreGC::Tag::Value;
    }

    void traverseLeft() noexcept;
    void traverseRight() noexcept;
public:    
    UnicodeRopeIterator(__UnicodeRope& root) noexcept : traversalStack(), inlineString(), isInline(false) {
        this->initializeTraversal(root);
    };

    UnicodeCharBuffer next() noexcept;

    inline bool hasNext() noexcept {
        return !this->traversalStack.empty() || this->isInline;
    }
};

// Will need to support Bosque CString and String eventually
typedef std::variant<Int, Nat, BigInt, BigNat, Float, Bool> MainType; 

//
// Converts return type of main to string
//
std::string to_string(MainType v) noexcept; 

} // namespace __CoreCpp

constexpr __CoreCpp::Int operator "" _i(unsigned long long v) { return __CoreCpp::Int(static_cast<int64_t>(v)); }
constexpr __CoreCpp::BigInt operator "" _I(const char* v) { return __CoreCpp::BigInt(v); }
constexpr __CoreCpp::Nat operator "" _n(unsigned long long v) { return __CoreCpp::Nat(static_cast<uint64_t>(v)); }
constexpr __CoreCpp::BigNat operator "" _N(const char* v) { return __CoreCpp::BigNat(v); }
constexpr __CoreCpp::Float operator "" _f(long double v) { return __CoreCpp::Float(static_cast<double>(v)); }

// For debugging
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Int& t);
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigInt& t);
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Nat& t);
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigNat& t);
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Float& t);
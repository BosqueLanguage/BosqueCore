#include "cppruntime.hpp"

namespace __CoreCpp {

ThreadLocalInfo& info = ThreadLocalInfo::get();

CCharBuffer CCharBuffer::create_empty() {
    return {{}, 0_n};
}
CCharBuffer CCharBuffer::create_1(CChar c1) {
    return {{c1}, 1_n};
}
CCharBuffer CCharBuffer::create_2(CChar c1, CChar c2) {
    return {{c1, c2}, 2_n};
}
CCharBuffer CCharBuffer::create_3(CChar c1, CChar c2, CChar c3) {
    return {{c1, c2, c3}, 3_n};
}
CCharBuffer CCharBuffer::create_4(CChar c1, CChar c2, CChar c3, CChar c4) {
    return {{c1, c2, c3, c4}, 4_n};
}
CCharBuffer CCharBuffer::create_5(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5) {
    return {{c1, c2, c3, c4, c5}, 5_n};
}
CCharBuffer CCharBuffer::create_6(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6) {
    return {{c1, c2, c3, c4, c5, c6}, 6_n};
}
CCharBuffer CCharBuffer::create_7(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6, CChar c7) {
    return {{c1, c2, c3, c4, c5, c6, c7}, 7_n};
}
CCharBuffer CCharBuffer::create_8(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6, CChar c7, CChar c8) {
    return {{c1, c2, c3, c4, c5, c6, c7, c8}, 8_n};
}

CCharBuffer cbufferFromStringLiteral(size_t ptr, size_t size, const CChar* &basestr) noexcept {
    const CChar* buf = basestr + ptr;
    switch(size) {
        case 0: return CCharBuffer::create_empty();
        case 1: return CCharBuffer::create_1(buf[0]);
        case 2: return CCharBuffer::create_2(buf[0], buf[1]);
        case 3: return CCharBuffer::create_3(buf[0], buf[1], buf[2]);
        case 4: return CCharBuffer::create_4(buf[0], buf[1], buf[2], buf[3]);
        case 5: return CCharBuffer::create_5(buf[0], buf[1], buf[2], buf[3], buf[4]);
        case 6: return CCharBuffer::create_6(buf[0], buf[1], buf[2], buf[3], buf[4], buf[5]);
        case 7: return CCharBuffer::create_7(buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6]);
        default: return CCharBuffer::create_8(buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7]);
    }
}

CCharBuffer cbufferFromNat(Nat v) noexcept {
    uint64_t val = v.get();
    const int radix = 10;

    CChar stack[maxCCharBufferSize] = {};
    CCharBuffer buf = {};
    int stacksize = 0;
    while(stacksize < maxCCharBufferSize) {
        if(val == 0) {
            break;
        }

        uint64_t dig = val % radix;
        val /= radix;

        stack[stacksize] = dig + '0'; 
        buf.size += 1_n;

        stacksize++;
    }

    // Chars are inserted into 'stack' initially in reverse order
    int i = stacksize - 1;
    while(i >= 0) {
        buf.chars[(stacksize - 1) - i] = stack[i];
        i--;
    }

    return buf;
}

// Moves chars from cb2 to cb1 until cb1 is full
CCharBuffer& cbufferMerge(CCharBuffer& cb1, CCharBuffer& cb2) noexcept {
    uint64_t cb1size = cb1.size.get();
    uint64_t cb2size = cb2.size.get();

    if(cb1size + cb2size >= maxCCharBufferSize) {
        cb1.size = Nat(maxCCharBufferSize);
    }
    else {
        cb1.size += cb2.size;
    }

    // We could probably make this loop tighter but its fine as is
    for(uint64_t i = cb1size; i < maxCCharBufferSize; i++) {
        cb1.chars[i] = cb2.chars[i - cb1size];
    }

    return cb1;
}

// Removes already merged chars from cb
CCharBuffer& cbufferRemainder(CCharBuffer& cb, Nat split) noexcept {
    uint64_t nsplit = split.get();

    if(nsplit == 0) {
        return cb;
    }

    for(uint64_t i = 0; i < maxCCharBufferSize; i++) {
        if(i < nsplit) {
            cb.chars[i] = 0;
            cb.size -= 1_n;
        }
        else {
            cb.chars[i - nsplit] = cb.chars[i];
            cb.chars[i] = 0;
        }
    }

    return cb;
}

static inline Bool cbuf_memcmp(CChar b1[maxCCharBufferSize], CChar b2[maxCCharBufferSize]) noexcept {
    static_assert(maxCCharBufferSize * sizeof(CChar) == sizeof(uintptr_t));
    
    return *reinterpret_cast<uintptr_t*>(b1) - *reinterpret_cast<uintptr_t*>(b2) == 0;
}

Bool cbufferEqual(CCharBuffer& cb1, CCharBuffer& cb2) noexcept {
    return cbuf_memcmp(cb1.chars, cb2.chars);
}

Bool cbufferLess(CCharBuffer& cb1, CCharBuffer& cb2) noexcept {
    for(int i = 0; i < maxCCharBufferSize; i++) {
        if(cb1.chars[i] != cb2.chars[i]) {
            return cb1.chars[i] < cb2.chars[i];
        }
    }
    return false;
}

Bool cbufferIsPrefix(CCharBuffer cb, CCharBuffer& pre) noexcept {
    const uint64_t presize = pre.size.get();
    if(presize > cb.size.get()) {
        return false;
    }
    
    for(uint64_t i = 0; i < presize; i++) {
        if(cb.chars[i] != pre.chars[i]) {
            return false;
        }
    }

    return true;
}

// Removes prefix from cb1, invariant is cb1 starts with pre
CCharBuffer& cbufferRemove(CCharBuffer& cb, CCharBuffer& pre) noexcept {
    assert(pre.size <= cb.size);
    
    const uint64_t remove_count = pre.size.get();
    
    // Shift chars not in pre then nuke whats left
    for(uint64_t i = 0; i < cb.size.get() - remove_count; i++) {
        cb.chars[i] = cb.chars[i + remove_count];
    }
    for(uint64_t i = cb.size.get() - remove_count; i < static_cast<uint64_t>(maxCCharBufferSize); i++) {
        cb.chars[i] = 0;
    }
    
    cb.size -= Nat(remove_count);
    return cb;
}


UnicodeCharBuffer UnicodeCharBuffer::create_empty() {
    return {{}, 0_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_1(UnicodeChar c1) {
    return {{c1}, 1_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_2(UnicodeChar c1, UnicodeChar c2) {
    return {{c1, c2}, 2_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_3(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3) {
    return {{c1, c2, c3}, 3_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_4(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4) {
    return {{c1, c2, c3, c4}, 4_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_5(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5) {
    return {{c1, c2, c3, c4, c5}, 5_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_6(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6) {
    return {{c1, c2, c3, c4, c5, c6}, 6_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_7(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6, UnicodeChar c7) {
    return {{c1, c2, c3, c4, c5, c6, c7}, 7_n};
}
UnicodeCharBuffer UnicodeCharBuffer::create_8(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6, UnicodeChar c7, UnicodeChar c8) {
    return {{c1, c2, c3, c4, c5, c6, c7, c8}, 8_n};
}

UnicodeCharBuffer ubufferFromStringLiteral(size_t ptr, size_t size, const UnicodeChar* &basestr) noexcept {
    const UnicodeChar* buf = basestr + ptr;
    switch(size) {
        case 0: return UnicodeCharBuffer::create_empty();
        case 1: return UnicodeCharBuffer::create_1(buf[0]);
        case 2: return UnicodeCharBuffer::create_2(buf[0], buf[1]);
        case 3: return UnicodeCharBuffer::create_3(buf[0], buf[1], buf[2]);
        case 4: return UnicodeCharBuffer::create_4(buf[0], buf[1], buf[2], buf[3]);
        case 5: return UnicodeCharBuffer::create_5(buf[0], buf[1], buf[2], buf[3], buf[4]);
        case 6: return UnicodeCharBuffer::create_6(buf[0], buf[1], buf[2], buf[3], buf[4], buf[5]);
        case 7: return UnicodeCharBuffer::create_7(buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6]);
        default: return UnicodeCharBuffer::create_8(buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7]);
    }
}
// Moves chars from ub2 to ub1 until ub1 is full
UnicodeCharBuffer& ubufferMerge(UnicodeCharBuffer& ub1, UnicodeCharBuffer& ub2) noexcept {
    uint64_t ub1size = ub1.size.get();
    uint64_t ub2size = ub2.size.get();

    if(ub1size + ub2size >= maxUnicodeCharBufferSize) {
        ub1.size = Nat(maxUnicodeCharBufferSize);
    }
    else {
        ub1.size += ub2.size;
    }

    // We could probably make this loop tighter but its fine as is
    for(uint64_t i = ub1size; i < maxUnicodeCharBufferSize; i++) {
        ub1.chars[i] = ub2.chars[i - ub1size];
    }

    return ub1;
}

// Removes already merged chars from ub
UnicodeCharBuffer& ubufferRemainder(UnicodeCharBuffer& ub, Nat split) noexcept {
    uint64_t nsplit = split.get();

    if(nsplit == 0) {
        return ub;
    }

    for(uint64_t i = 0; i < maxUnicodeCharBufferSize; i++) {
        if(i < nsplit) {
            ub.chars[i] = 0;
            ub.size -= 1_n;
        }
        else {
            ub.chars[i - nsplit] = ub.chars[i];
            ub.chars[i] = 0;
        }
    }

    return ub;
}

std::string to_string(MainType v) noexcept {
    if(std::holds_alternative<Bool>(v)) {
        Bool res = std::get<Bool>(v);
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

// For debugging
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Int& t) { return os << t.get() << "_i"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigInt& t) { return os << __CoreCpp::t_to_string<__int128_t>(t.get()) << "_I"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Nat& t) { return os << t.get() << "_n"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigNat& t) { return os << __CoreCpp::t_to_string<__uint128_t>(t.get()) << "_N"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Float& t) { return os << t.get() << "_f"; }
#include "cppruntime.hpp"

namespace __CoreCpp {

ThreadLocalInfo& info = ThreadLocalInfo::get();
    
PathStack PathStack::create() {
    return {0, 0};
}
PathStack PathStack::left() const {
    return { bits << 1, index + 1 };
}
PathStack PathStack::right() const {
    return { bits << 1 | 1, index + 1 };
}
PathStack PathStack::up() const {
    return { bits >> 1, index - 1 };
}

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

// Moves chars from cb1 to cb2 until cb1 is full
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

std::string to_string(MainType v) noexcept {
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

// For debugging
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Int& t) { return os << t.get() << "_i"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigInt& t) { return os << __CoreCpp::t_to_string<__int128_t>(t.get()) << "_I"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Nat& t) { return os << t.get() << "_n"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::BigNat& t) { return os << __CoreCpp::t_to_string<__uint128_t>(t.get()) << "_N"; }
std::ostream& operator<<(std::ostream &os, const __CoreCpp::Float& t) { return os << t.get() << "_f"; }
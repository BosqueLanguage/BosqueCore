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

CCharBuffer cbufferFromStringLiteral(size_t size, const CChar* &basestr) noexcept {
    const CChar* buf = basestr;
    basestr += 8;

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

    CChar stack[maxCCharBufSize] = {};
    CCharBuffer buf = {};
    int stacksize = 0;
    while(stacksize < maxCCharBufSize) {
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

// A little bit funny but ensures cb2's updates are reflected at runtime
Tuple2<maxCCharBufSize / 8, maxCCharBufSize / 8> cbufferMerge2(CCharBuffer& cb1, CCharBuffer& cb2) noexcept {
    uint64_t cb1size = cb1.size.get();
    for(uint64_t i = cb1size; i < maxCCharBufSize; i++) {
        uint64_t cb2_idx = i - cb1size;
        cb1.chars[i] = cb2.chars[cb2_idx];
        cb2.chars[cb2_idx] = 0;

        // Could we make this better?
        uint64_t cb2_remainder = (maxCCharBufSize - cb1size) + (i - cb1size);
        if(cb2_remainder < maxCCharBufSize) {
            cb2.chars[cb2_idx] = cb2.chars[cb2_remainder];
            cb2.chars[cb2_remainder] = 0;
        }

        cb1.size += 1_n;
        cb2.size -= 1_n;
    }

    return Tuple2<maxCCharBufSize / 8, maxCCharBufSize / 8>(cb1, cb2);
}

// Case when cb1.size + cb2.size <= maxCCharBufferSize
CCharBuffer& cbufferMerge(CCharBuffer& cb1, CCharBuffer& cb2) noexcept {
    uint64_t i = cb1.size.get();
    while(i <= maxCCharBufSize) {
        cb1.chars[i] = cb2.chars[maxCCharBufSize - i];
    }

    return cb1;
}

// This code works but is heinousely over-engineered.
    /*
    uint64_t cb1size = cb1.size.get();
    for(uint64_t i = cb1size; i < maxCCharBufSize; i++) {
        uint64_t cb2_idx = i - cb1size;
        cb1.chars[i] = cb2.chars[cb2_idx];
        cb2.chars[cb2_idx] = 0;
        
        // Could we make this better?
        uint64_t cb2_remainder = (maxCCharBufSize - cb1size) + (i - cb1size);
        if(cb2_remainder < maxCCharBufSize) {
            cb2.chars[cb2_idx] = cb2.chars[cb2_remainder];
            cb2.chars[cb2_remainder] = 0;
        }
        
        cb1.size += 1_n;
        cb2.size -= 1_n;
    }
    return cb1;
    */

// Hmm this also blows maybe my origin al code was better
/* 
    CChar buf[maxCCharBufSize * 2] = {};
    Nat size = cb1.size + cb2.size;
    uint64_t cb1_size = cb1.size.get();
    uint64_t buf_i = 0;
    uint64_t cb_i = 0;
    uint64_t max_charpos = cb1.size.get();
    while(buf_i < size.get()) {
        if(cb_i == max_charpos) {
            max_charpos = cb2.size.get();
            cb_i = 0;
        }
        CChar cur = 0;
        if(buf_i < cb1_size) {
            cur = cb1.chars[cb_i];
        }
        else {
            cur = cb2.chars[cb_i];
        }
        buf[buf_i] = cur;
    }
    &cb1.chars = reinterpret_cast<CChar*>(buf);
    &cb2.chars = reinterpret_cast<CChar*>(buf + maxCCharBufSize);
    return Tuple2<maxCCharBufSize / 8, maxCCharBufSize / 8>(cb1, cb2);
*/ 



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
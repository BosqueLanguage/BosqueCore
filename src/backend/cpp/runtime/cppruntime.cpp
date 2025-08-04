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
    return {{}, 0};
}
CCharBuffer CCharBuffer::create_1(CChar c1) {
    return {{c1}, 1};
}
CCharBuffer CCharBuffer::create_2(CChar c1, CChar c2) {
    return {{c1, c2}, 2};
}
CCharBuffer CCharBuffer::create_3(CChar c1, CChar c2, CChar c3) {
    return {{c1, c2, c3}, 3};
}
CCharBuffer CCharBuffer::create_4(CChar c1, CChar c2, CChar c3, CChar c4) {
    return {{c1, c2, c3, c4}, 4};
}
CCharBuffer CCharBuffer::create_5(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5) {
    return {{c1, c2, c3, c4, c5}, 5};
}
CCharBuffer CCharBuffer::create_6(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6) {
    return {{c1, c2, c3, c4, c5, c6}, 6};
}
CCharBuffer CCharBuffer::create_7(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6, CChar c7) {
    return {{c1, c2, c3, c4, c5, c6, c7}, 7};
}
CCharBuffer CCharBuffer::create_8(CChar c1, CChar c2, CChar c3, CChar c4, CChar c5, CChar c6, CChar c7, CChar c8) {
    return {{c1, c2, c3, c4, c5, c6, c7, c8}, 8};
}

UnicodeCharBuffer UnicodeCharBuffer::create_empty() {
    return {{}, 0};
}
UnicodeCharBuffer UnicodeCharBuffer::create_1(UnicodeChar c1) {
    return {{c1}, 1};
}
UnicodeCharBuffer UnicodeCharBuffer::create_2(UnicodeChar c1, UnicodeChar c2) {
    return {{c1, c2}, 2};
}
UnicodeCharBuffer UnicodeCharBuffer::create_3(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3) {
    return {{c1, c2, c3}, 3};
}
UnicodeCharBuffer UnicodeCharBuffer::create_4(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4) {
    return {{c1, c2, c3, c4}, 4};
}
UnicodeCharBuffer UnicodeCharBuffer::create_5(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5) {
    return {{c1, c2, c3, c4, c5}, 5};
}
UnicodeCharBuffer UnicodeCharBuffer::create_6(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6) {
    return {{c1, c2, c3, c4, c5, c6}, 6};
}
UnicodeCharBuffer UnicodeCharBuffer::create_7(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6, UnicodeChar c7) {
    return {{c1, c2, c3, c4, c5, c6, c7}, 7};
}
UnicodeCharBuffer UnicodeCharBuffer::create_8(UnicodeChar c1, UnicodeChar c2, UnicodeChar c3, UnicodeChar c4, UnicodeChar c5, UnicodeChar c6, UnicodeChar c7, UnicodeChar c8) {
    return {{c1, c2, c3, c4, c5, c6, c7, c8}, 8};
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
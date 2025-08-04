#include "cppruntime.hpp"

namespace __CoreCpp {

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

} // namespace __CoreCpp
#include "cppruntime.hpp"

PathStack PathStack::create() {
    return {0, 0};
}
PathStack PathStack::left() const {
    return { bits << 1 };
}
PathStack PathStack::right() const {
    return { bits << 1 | 1 };
}
PathStack PathStack::up() const {
    return { bits >> 1 };
}

CCharBuffer CCharBuffer::create_empty() {
    return {{}, 0};
}
CCharBuffer CCharBuffer::create_1(uint8_t c1) {
    return {{c1}, 1};
}
CCharBuffer CCharBuffer::create_2(uint8_t c1, uint8_t c2) {
    return {{c1, c2}, 2};
}
CCharBuffer CCharBuffer::create_3(uint8_t c1, uint8_t c2, uint8_t c3) {
    return {{c1, c2, c3}, 3};
}
CCharBuffer CCharBuffer::create_4(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4) {
    return {{c1, c2, c3, c4}, 4};
}
CCharBuffer CCharBuffer::create_5(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5) {
    return {{c1, c2, c3, c4, c5}, 5};
}
CCharBuffer CCharBuffer::create_6(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5, uint8_t c6) {
    return {{c1, c2, c3, c4, c5, c6}, 6};
}
CCharBuffer CCharBuffer::create_7(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5, uint8_t c6, uint8_t c7) {
    return {{c1, c2, c3, c4, c5, c6, c7}, 7};
}
CCharBuffer CCharBuffer::create_8(uint8_t c1, uint8_t c2, uint8_t c3, uint8_t c4, uint8_t c5, uint8_t c6, uint8_t c7, uint8_t c8) {
    return {{c1, c2, c3, c4, c5, c6, c7, c8}, 8};
}

UnicodeCharBuffer UnicodeCharBuffer::create_empty() {
    return {{}, 0};
}
UnicodeCharBuffer UnicodeCharBuffer::create_1(uint32_t c1) {
    return {{c1}, 1};
}
UnicodeCharBuffer UnicodeCharBuffer::create_2(uint32_t c1, uint32_t c2) {
    return {{c1, c2}, 2};
}
UnicodeCharBuffer UnicodeCharBuffer::create_3(uint32_t c1, uint32_t c2, uint32_t c3) {
    return {{c1, c2, c3}, 3};
}
UnicodeCharBuffer UnicodeCharBuffer::create_4(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4) {
    return {{c1, c2, c3, c4}, 4};
}
UnicodeCharBuffer UnicodeCharBuffer::create_5(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5) {
    return {{c1, c2, c3, c4, c5}, 5};
}
UnicodeCharBuffer UnicodeCharBuffer::create_6(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5, uint32_t c6) {
    return {{c1, c2, c3, c4, c5, c6}, 6};
}
UnicodeCharBuffer UnicodeCharBuffer::create_7(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5, uint32_t c6, uint32_t c7) {
    return {{c1, c2, c3, c4, c5, c6, c7}, 7};
}
UnicodeCharBuffer UnicodeCharBuffer::create_8(uint32_t c1, uint32_t c2, uint32_t c3, uint32_t c4, uint32_t c5, uint32_t c6, uint32_t c7, uint32_t c8) {
    return {{c1, c2, c3, c4, c5, c6, c7, c8}, 8};
}
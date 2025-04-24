#pragma once

#include <stdint.h>

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
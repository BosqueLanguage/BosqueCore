#pragma once

#include <stdint.h>

// Useful for keeping track of path in tree iteration
struct PathStack {
    uint64_t bits;
    int index;

    PathStack create() const;
    PathStack left() const;
    PathStack right() const;
    PathStack up() const;
};

// We say for now no more than 8 chars, may want to make this dynamically pick 8 or 16 max
struct CCharBuffer {
    uint8_t chars[16];
    int index;

    // Would be some functions here to modify this buffer
};

struct UnicodeCharBuffer {
    uint32_t chars[16];
    int index;

    // Would be some functions here to modify this buffer
};
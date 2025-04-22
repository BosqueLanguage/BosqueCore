#pragma once

#include <stdint.h>

//
// This file will be included in order to call provided cpp functions in emitted cpp files
//

// Useful for keeping track of path in tree iterations
struct PathStack {
    uint64_t bits;

    PathStack create() const;
    PathStack left() const;
    PathStack right() const;
    PathStack up() const;
};

// We say for now no more than 16 chars, may want to make this dynamically pick 8 or 16 max
struct CCharBuffer {
    uint8_t chars[16];
    int index;

    // Would be some functions here to modify this buffer
};

struct UnicodeCharBuffer {
    uint8_t chars[16];
    int index;

    // Would be some functions here to modify this buffer
};
#include "cppruntime.hpp"

PathStack PathStack::create() const {
    return {0};
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
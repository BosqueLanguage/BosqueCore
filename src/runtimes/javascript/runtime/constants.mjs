"use strict";

//2^53 - 1 ## this way (1) negation and conversion MInt<->MNat is always safe (2) we can steal the top bit for tagging on Int/Nat later
const FIXED_NUMBER_MAX = Number.MAX_SAFE_INTEGER;
const FIXED_NUMBER_MIN = Number.MIN_SAFE_INTEGER; 

export {
    FIXED_NUMBER_MAX, FIXED_NUMBER_MIN
};

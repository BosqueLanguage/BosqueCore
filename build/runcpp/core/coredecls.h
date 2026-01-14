#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

#include "bools.h"
#include "chars.h"
#include "integrals.h"
#include "fpoints.h"
#include "strings.h"

constexpr ᐸRuntimeᐳ::XNone none = ᐸRuntimeᐳ::xnone;

constexpr ᐸRuntimeᐳ::XBool FALSE = ᐸRuntimeᐳ::XFALSE;
constexpr ᐸRuntimeᐳ::XBool TRUE = ᐸRuntimeᐳ::XTRUE;

constexpr ᐸRuntimeᐳ::XNat operator""_n(unsigned long long n)
{
    return ᐸRuntimeᐳ::XNat{(int64_t)n};
}

constexpr ᐸRuntimeᐳ::XInt operator""_i(unsigned long long n)
{
    return ᐸRuntimeᐳ::XInt{(int64_t)n};
}

constexpr ᐸRuntimeᐳ::XChkNat operator""_N(unsigned long long n)
{
    return ᐸRuntimeᐳ::XChkNat{(__int128_t)n};
}
    
constexpr ᐸRuntimeᐳ::XChkInt operator""_I(unsigned long long n)
{
    return ᐸRuntimeᐳ::XChkInt{(__int128_t)n};
}

constexpr ᐸRuntimeᐳ::XFloat operator""_f(long double n)
{
    return ᐸRuntimeᐳ::XFloat{(double)n};
}

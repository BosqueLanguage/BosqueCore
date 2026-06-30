#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

#include "bools.h"
#include "chars.h"
#include "integrals.h"
#include "fpoints.h"
#include "strings.h"

inline constexpr ᐸRuntimeᐳ::XNone none = ᐸRuntimeᐳ::xnone;

inline constexpr ᐸRuntimeᐳ::XBool FALSE = ᐸRuntimeᐳ::XFALSE;
inline constexpr ᐸRuntimeᐳ::XBool TRUE = ᐸRuntimeᐳ::XTRUE;

consteval ᐸRuntimeᐳ::XNat operator""_n(unsigned long long n)
{
    return ᐸRuntimeᐳ::XNat{(int64_t)n};
}

consteval ᐸRuntimeᐳ::XInt operator""_i(unsigned long long n)
{
    return ᐸRuntimeᐳ::XInt{(int64_t)n};
}

consteval ᐸRuntimeᐳ::XChkNat operator""_N(unsigned long long n)
{
    return ᐸRuntimeᐳ::XChkNat{(__int128_t)n};
}
    
consteval ᐸRuntimeᐳ::XChkInt operator""_I(unsigned long long n)
{
    return ᐸRuntimeᐳ::XChkInt{(__int128_t)n};
}

consteval ᐸRuntimeᐳ::XFloat operator""_f(long double n)
{
    return ᐸRuntimeᐳ::XFloat{(double)n};
}

template<ᐸRuntimeᐳ::CStrRootInlineContent::SmallLiteralInitBuffer ssb>
inline ᐸRuntimeᐳ::XCString operator""_cs()
{
    return ᐸRuntimeᐳ::XCString{ᐸRuntimeᐳ::CStrRootInlineContent(ssb)};
}

template<ᐸRuntimeᐳ::StrRootInlineContent::SmallLiteralInitBuffer ssb>
inline ᐸRuntimeᐳ::XString operator""_us()
{
    return ᐸRuntimeᐳ::XString{ᐸRuntimeᐳ::StrRootInlineContent(ssb)};
}

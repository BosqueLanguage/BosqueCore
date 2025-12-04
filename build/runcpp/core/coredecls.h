#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

#include "bools.h"
#include "chars.h"
#include "integrals.h"
#include "fpoints.h"
#include "strings.h"

using None = uint64_t;
constexpr None none = 0ull;

constexpr ᐸRuntimeᐳ::Bool FALSE = ᐸRuntimeᐳ::Bool::from(false);
constexpr ᐸRuntimeᐳ::Bool TRUE = ᐸRuntimeᐳ::Bool::from(true);

constexpr ᐸRuntimeᐳ::Nat operator""_n(unsigned long long n)
{
    return ᐸRuntimeᐳ::Nat(n);
}

constexpr ᐸRuntimeᐳ::Int operator""_i(unsigned long long n)
{
    return ᐸRuntimeᐳ::Int(n);
}

constexpr ᐸRuntimeᐳ::ChkNat operator""_N(unsigned long long n)
{
    return ᐸRuntimeᐳ::ChkNat(n);
}
    
constexpr ᐸRuntimeᐳ::ChkInt operator""_I(unsigned long long n)
{
    return ᐸRuntimeᐳ::ChkInt(n);
}

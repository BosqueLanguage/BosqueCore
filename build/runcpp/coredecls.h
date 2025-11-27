#pragma once

#include "./common.h"

#include "./bsqtype.h"
#include "./boxed.h"

#include "./core/bools.h"
#include "./core/chars.h"
#include "./core/integrals.h"
#include "./core/fpoints.h"
#include "./core/strings.h"


namespace Core
{
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
}

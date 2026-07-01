#pragma once

#include <vector>
#include <string>

#define BSQ_REGISTER_FLAG(NAME, DESCRIPTION) constexpr bool g_bsq_##NAME = (bool)NAME
#define GC_REGISTER_FLAG(NAME, DESCRIPTION) constexpr bool g_gc_##NAME = (bool)ACTUAL
#define GC_REGISTER_PARAMETER(TYPE, NAME, DESCRIPTION) constexpr TYPE g_gc_##NAME = (TYPE)NAME
#define GC_REGISTER_PARAMETER_DEFAULT(TYPE, NAME, VALUE) constexpr TYPE g_gc_##NAME = (TYPE)(VALUE)

#define BSQ_IS_ENABLED(NAME) (ᐸRuntimeᐳ::g_bsq_##NAME)
#define GC_IS_ENABLED(NAME) (ᐸRuntimeᐳ::g_gc_##NAME)
#define GC_GET_PARAMETER(NAME) (ᐸRuntimeᐳ::g_gc_##NAME)

#define BSQ_ENSURE_FLAG_DEPS(NAME, ...) static_assert(!BSQ_IS_ENABLED(NAME) || ᐸRuntimeᐳ::_flags_allEnabled({__VA_ARGS__}), "Flag " #NAME " missing dependencies")

#define BSQ_IF_ENABLED(NAME, OP) if constexpr (BSQ_IS_ENABLED(NAME)) { OP; }
#define GC_IF_ENABLED(NAME, OP) if constexpr (GC_IS_ENABLED(NAME)) { OP; }

namespace ᐸRuntimeᐳ
{
    consteval bool _flags_allEnabled(const std::initializer_list<bool> flags) 
    {
        return std::all_of(flags.begin(), flags.end(), [](bool f) { return f; });
    }
}

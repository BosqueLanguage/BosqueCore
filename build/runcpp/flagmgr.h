#pragma once

#include <vector>
#include <string>

#define BSQ_MACRO_MAGIC_SECOND_ARG(A,B,...) B
#define BSQ_MACRO_MAGIC_CONCAT2(A,B) A ## B

#define BSQ_MACRO_MAGIC_DETECT_EXIST_TRUE ~,1

#define BSQ_MACRO_MAGIC_DETECT_EXIST(X) BSQ_MACRO_MAGIC_DETECT_EXIST_IMPL(BSQ_MACRO_MAGIC_CONCAT2(BSQ_MACRO_MAGIC_DETECT_EXIST_TRUE,X), 0)
#define BSQ_MACRO_MAGIC_DETECT_EXIST_IMPL(...) BSQ_MACRO_MAGIC_SECOND_ARG(__VA_ARGS__)

#define BSQ_REGISTER_FLAG(NAME, DESCRIPTION) constexpr bool g_bsq_ ## NAME = (bool)(BSQ_MACRO_MAGIC_DETECT_EXIST(NAME))
#define GC_REGISTER_FLAG(NAME, DESCRIPTION) constexpr bool g_gc_ ## NAME = (bool)(BSQ_MACRO_MAGIC_DETECT_EXIST(NAME))
#define GC_REGISTER_PARAMETER(TYPE, NAME, DESCRIPTION) constexpr TYPE g_gc_ ## NAME = (TYPE)NAME
#define GC_REGISTER_PARAMETER_DEFAULT(TYPE, NAME, VALUE) constexpr TYPE g_gc_ ## NAME = (TYPE)(VALUE)

#define BSQ_IS_ENABLED(NAME) (ᐸRuntimeᐳ::g_bsq_ ## NAME)
#define GC_IS_ENABLED(NAME) (ᐸRuntimeᐳ::g_gc_ ## NAME)
#define GC_GET_PARAMETER(NAME) (ᐸRuntimeᐳ::g_gc_ ## NAME)

#define BSQ_ENSURE_FLAG_DEPS(NAME, ...) static_assert(!BSQ_IS_ENABLED(NAME) || ᐸRuntimeᐳ::_flags_allEnabled({__VA_ARGS__}), "Flag " #NAME " missing dependencies")

#define BSQ_IF_ENABLED(NAME, OP) if constexpr (ᐸRuntimeᐳ::g_bsq_ ## NAME) { OP; }
#define GC_IF_ENABLED(NAME, OP) if constexpr (ᐸRuntimeᐳ::g_gc_ ## NAME) { OP; }

namespace ᐸRuntimeᐳ
{
    consteval bool _flags_allEnabled(const std::initializer_list<bool> flags) 
    {
        return std::all_of(flags.begin(), flags.end(), [](bool f) { return f; });
    }
}

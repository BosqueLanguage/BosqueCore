#pragma once

#include "lexer.h"

#include "../../common.h"
#include "../../core/bools.h"
#include "../../core/chars.h"
#include "../../core/integrals.h"
#include "../../core/strings.h"

namespace ᐸRuntimeᐳ
{
    class BSQONParser
    {
    private:
        BSQONLexer lexer;

    public:
        BSQONParser(ByteBufferIterator iter) noexcept : lexer(iter) {}

        std::optional<None> parseNone() noexcept;
        std::optional<Bool> parseBool() noexcept;
        std::optional<Nat> parseNat() noexcept;
        std::optional<Int> parseInt() noexcept;
        std::optional<ChkNat> parseChkNat() noexcept;
        std::optional<ChkInt> parseChkInt() noexcept;
    };

    class JSONParser
    {
    private:
    };
}

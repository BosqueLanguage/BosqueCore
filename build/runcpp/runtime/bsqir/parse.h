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
        BSQONParser(ByteBufferIterator iter) : lexer(iter) {}

        std::optional<None> parseNone();
        std::optional<Bool> parseBool();
        std::optional<Nat> parseNat();
        std::optional<Int> parseInt();
        std::optional<ChkNat> parseChkNat();
        std::optional<ChkInt> parseChkInt();
    };

    class JSONParser
    {
    private:
    };
}

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
        BSQONParser() : lexer() {}

        void initialize(std::list<uint8_t*>&& iobuffs);
        void release();

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

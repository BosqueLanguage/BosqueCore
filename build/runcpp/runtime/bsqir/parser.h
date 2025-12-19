#pragma once

#include "lexer.h"

#include "../../common.h"
#include "../../core/coredecls.h"
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

        std::optional<XNone> parseNone();
        std::optional<XBool> parseBool();
        std::optional<XNat> parseNat();
        std::optional<XInt> parseInt();
        std::optional<XChkNat> parseChkNat();
        std::optional<XChkInt> parseChkInt();
    };

    class JSONParser
    {
    private:
    };
}

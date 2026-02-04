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

        void initialize(std::list<uint8_t*>&& iobuffs, size_t totalbytes);
        void release();

        bool peekSymbol(char sym);
        BSQONTokenType peekTokenType();

        bool testType(const char* tname);
        bool ensureAndConsumeType(const char* tname);
        
        bool ensureAndConsumeSymbol(char sym)
        {
            auto token = this->lexer.current();
            if(!(token.tokentype == BSQONTokenType::LiteralSymbol)) {
                return false;
            }

            if(token.extract() != sym) {
                return false;
            }

            this->lexer.consume();
            return true;
        }
        
        template<size_t len>
        bool ensureAndConsumeSymbol(const char (&sym)[len])
        {
            auto token = this->lexer.current();
            if(token.tokentype != BSQONTokenType::LiteralSymbol) {
                return false;
            }

            if(!this->lexer.current().xmatches(sym)) {
                return false;
            }

            this->lexer.consume();
            return true;
        }

        template<size_t len>
        bool ensureAndConsumeKeyword(const char (&kw)[len])
        {
            auto token = this->lexer.current();
            if(token.tokentype != BSQONTokenType::LiteralKeyword) {
                return false;
            }

            if(!this->lexer.current().xmatches(kw)) {
                return false;
            }

            this->lexer.consume();
            return true;
        }

        bool ensureAndConsumeIdentifier(char* outident, size_t maxlen);

        void consumeTokenAlways();
        bool testAndConsumeTokenIf(BSQONTokenType ttype);

        std::optional<XNone> parseNone();
        std::optional<XBool> parseBool();
        std::optional<XNat> parseNat();
        std::optional<XInt> parseInt();
        std::optional<XChkNat> parseChkNat();
        std::optional<XChkInt> parseChkInt();

        std::optional<XFloat> parseFloat();

        std::optional<XCString> parseCString();
        std::optional<XString> parseString();

        bool allInputConsumed()
        {
            return this->lexer.current().tokentype == BSQONTokenType::EOFToken;
        }
    };

    class JSONParser
    {
    private:
    };
}

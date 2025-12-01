#include "lexer.h"

#include <bitset>

namespace ᐸRuntimeᐳ
{
    using REState = std::bitset<32>;

    bool BSQONLexer::testchar(const ByteBufferIterator& ii, char c)
    {
        return ii.valid() && (ii.get() == static_cast<uint8_t>(c));
    }
        
    bool BSQONLexer::testchars(ByteBufferIterator ii, const char* chars)
    {
        while(*chars != '\0') {
            if(!ii.valid() || (ii.get() != static_cast<uint8_t>(*chars))) {
                return false;
            }

            ii.next();
            chars++;
        }

        return true;
    }

    bool BSQONLexer::tryLexNone()
    {
        if(BSQONLexer::testchars(this->iter, "none")) {
            this->ctoken.tokentype = BSQONTokenType::LiteralNone;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 4);
            return true;
        }

        return false;
    }

    bool BSQONLexer::tryLexBool()
    {
        if(BSQONLexer::testchars(this->iter, "true")) {
            this->ctoken.tokentype = BSQONTokenType::LiteralTrue;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 4);
            return true;
        }
        else if(BSQONLexer::testchars(this->iter, "false")) {
            this->ctoken.tokentype = BSQONTokenType::LiteralFalse;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 5);
            return true;
        }

        return false;
    }

    bool BSQONLexer::lexIntegralHelper(bool negok, char suffix)
    {
        ByteBufferIterator ii = this->iter;
        size_t startidx = ii.getIndex();
        size_t endidx = std::numeric_limits<size_t>::max();

        //This is a simple DFA for nat values (non-negative integers) as a loop with checks
        REState states;
        constexpr size_t STATE_START = 0;

        constexpr size_t STATE_PLUS = 1;
        constexpr size_t STATE_MINUS = 2;

        constexpr size_t STATE_NONZERO = 3;

        constexpr size_t STATE_SUFFIX = 4;
        constexpr size_t STATE_ACCEPT = 5;

        while(!states.none() && ii.valid()) {
            const char c = (char)ii.get();

            REState postInit = 0;
            if(states.test(STATE_START)) {
                if(c == '0') {
                    postInit.set(STATE_SUFFIX);
                }
                if(('1' <= c) & (c <= '9')) {
                    postInit.set(STATE_NONZERO);
                }
                if(c == '+') {
                    postInit.set(STATE_PLUS);
                }
                if(negok & (c == '-')) {
                    postInit.set(STATE_MINUS);
                }
            }

            REState postPlus = 0;
            if(states.test(STATE_PLUS)) {
                if(c == '0') {
                    postPlus.set(STATE_SUFFIX);
                }
                if(('1' <= c) & (c <= '9')) {
                    postPlus.set(STATE_NONZERO);
                }
            }

            REState postMinus = 0;
            if(states.test(STATE_MINUS)) {
                if(c == '0') {
                    postMinus.set(STATE_SUFFIX);
                }
                if(('1' <= c) & (c <= '9')) {
                    postMinus.set(STATE_NONZERO);
                }
            }

            REState postNonzero = 0;
            if(states.test(STATE_NONZERO)) {
                if(('0' <= c) & (c <= '9')) {
                    postNonzero.set(STATE_NONZERO);
                }
                postNonzero.set(STATE_SUFFIX);
            }

            REState postSuffix = 0;
            if(states.test(STATE_SUFFIX)) {
                if(c == suffix) {
                    postSuffix.set(STATE_ACCEPT);
                }
            }

            states = postInit | postPlus | postMinus | postNonzero | postSuffix;
            if(states.test(STATE_ACCEPT)) {
                endidx = ii.getIndex();
            }
        }

        if(endidx != std::numeric_limits<size_t>::max()) {
            this->ctoken.tokentype = BSQONTokenType::LiteralNat;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, endidx - startidx);
            return true;
        }

        return false;
    }

    bool BSQONLexer::tryLexNat()
    {
        return this->lexIntegralHelper(false, 'n');
    }

    bool BSQONLexer::tryLexInt()
    {
        return this->lexIntegralHelper(true, 'i');
    }
    
    bool BSQONLexer::tryLexChkNat()
    {
        if(this->testchar(this->iter, '#')) {
            this->ctoken.tokentype = BSQONTokenType::LiteralChkNat;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 1);
            return true;
        }

        return this->lexIntegralHelper(false, 'N');
    }

    bool BSQONLexer::tryLexChkInt()
    {
        if(this->testchar(this->iter, '#')) {
            this->ctoken.tokentype = BSQONTokenType::LiteralChkInt;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 1);
            return true;
        }

        return this->lexIntegralHelper(true, 'I');
    }

    void BSQONLexer::consume()
    {
        if(!this->iter.valid()) {
            this->ctoken.tokentype = BSQONTokenType::EOFToken;
            return;
        }

        if(this->tryLexNone()) {
            return;
        }
        else if(this->tryLexBool()) {
            return;
        }
        else if(this->tryLexNat() || this->tryLexInt() || this->tryLexChkNat() || this->tryLexChkInt()) {
            return;
        }
        else {
            this->ctoken.tokentype = BSQONTokenType::ErrorToken;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 1);
            return;
        }
    }
}

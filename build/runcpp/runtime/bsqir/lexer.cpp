#include "lexer.h"

namespace ᐸRuntimeᐳ
{
    using REState = uint8_t[32];

    void BSQONLexer::initialize(std::list<uint8_t*>&& iobuffs, size_t totalbytes)
    {
        this->iobuffs = std::move(iobuffs);
        this->iter.initialize(this->iobuffs.begin(), totalbytes);
        this->ctoken.clear();
    }

    void BSQONLexer::release()
    {
        for(auto iter = this->iobuffs.begin(); iter != this->iobuffs.end(); iter++) {
            g_alloc_info.io_buffer_free(*iter);
        }

        this->iobuffs.clear();
        this->iter.clear(this->iobuffs.end());
        this->ctoken.clear();
    }

    bool BSQONLexer::testchar(const BSQLexBufferIterator& ii, char c)
    {
        return ii.valid() && (ii.get() == static_cast<uint8_t>(c));
    }
        
    bool BSQONLexer::testchars(BSQLexBufferIterator ii, const char* chars)
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
        BSQLexBufferIterator ii = this->iter;
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

        while(std::find(states, states + 32, 1) != (states + 32) && ii.valid()) {
            const char c = (char)ii.get();
            REState next = {0};

            if(states[STATE_START]) {
                if(c == '0') {
                    next[STATE_SUFFIX] = 1;
                }
                if(('1' <= c) & (c <= '9')) {
                    next[STATE_NONZERO] = 1;
                }
                if(c == '+') {
                    next[STATE_PLUS] = 1;
                }
                if(negok & (c == '-')) {
                    next[STATE_MINUS] = 1;
                }
            }

            if(states[STATE_PLUS]) {
                if(c == '0') {
                    next[STATE_SUFFIX] = 1;
                }
                if(('1' <= c) & (c <= '9')) {
                    next[STATE_NONZERO] = 1;
                }
            }

            if(states[STATE_MINUS]) {
                if(c == '0') {
                    next[STATE_SUFFIX] = 1;
                }
                if(('1' <= c) & (c <= '9')) {
                    next[STATE_NONZERO] = 1;
                }
            }

            if(states[STATE_NONZERO]) {
                if(('0' <= c) & (c <= '9')) {
                    next[STATE_NONZERO] = 1;
                }
                next[STATE_SUFFIX] = 1;
            }

            if(states[STATE_SUFFIX]) {
                if(c == suffix) {
                    next[STATE_ACCEPT] = 1;
                }
            }

            std::memcpy(states, next, sizeof(REState));
            if(states[STATE_ACCEPT]) {
                endidx = ii.getIndex();
            }

            ii.next();
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

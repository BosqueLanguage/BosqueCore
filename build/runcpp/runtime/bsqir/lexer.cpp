#include "lexer.h"

namespace ᐸRuntimeᐳ
{
    using REState = uint8_t[32];

    void BSQONLexer::initialize(std::list<uint8_t*>&& iobuffs, size_t totalbytes)
    {
        this->iobuffs = std::move(iobuffs);
        this->iter = BSQLexBufferIterator(this->iobuffs.begin(), totalbytes);
        this->ctoken.clear();

        //now "consume" the invalid token to get the first token
        this->consume(); 
    }

    void BSQONLexer::release()
    {
        for(auto iter = this->iobuffs.begin(); iter != this->iobuffs.end(); iter++) {
            g_alloc_info.io_buffer_free(*iter);
        }

        this->iobuffs.clear();
        this->iter.reset();
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
            this->advanceToken(BSQONTokenType::LiteralNone, sizeof("none") - 1);
            return true;
        }

        return false;
    }

    bool BSQONLexer::tryLexBool()
    {
        if(BSQONLexer::testchars(this->iter, "true")) {
            this->advanceToken(BSQONTokenType::LiteralTrue, sizeof("true") - 1);
            return true;
        }
        else if(BSQONLexer::testchars(this->iter, "false")) {
            this->advanceToken(BSQONTokenType::LiteralFalse, sizeof("false") - 1);
            return true;
        }

        return false;
    }

    bool BSQONLexer::lexIntegralHelper(bool negok, char suffix, BSQONTokenType ltoken)
    {
        BSQLexBufferIterator ii = this->iter;
        size_t startidx = ii.getIndex();
        size_t endidx = std::numeric_limits<size_t>::max();

        //This is a simple DFA for nat values (non-negative integers) as a loop with checks
        constexpr size_t STATE_START = 0;

        constexpr size_t STATE_PLUS = 1;
        constexpr size_t STATE_MINUS = 2;

        constexpr size_t STATE_NONZERO = 3;

        constexpr size_t STATE_SUFFIX = 4;
        constexpr size_t STATE_ACCEPT = 5;

        REState states = {0};
        states[STATE_START] = 1;

        while(std::find(states, states + 32, 1) != (states + 32) && ii.valid()) {
            const char c = (char)ii.get();
            REState next = {0};

            if(states[STATE_START]) {
                if(c == '0') {
                    next[STATE_SUFFIX] = 1;
                }
                if(('1' <= c) & (c <= '9')) {
                    next[STATE_NONZERO] = 1;
                    next[STATE_SUFFIX] = 1;
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
                    next[STATE_SUFFIX] = 1;
                }
            }

            if(states[STATE_MINUS]) {
                if(c == '0') {
                    next[STATE_SUFFIX] = 1;
                }
                if(('1' <= c) & (c <= '9')) {
                    next[STATE_NONZERO] = 1;
                    next[STATE_SUFFIX] = 1;
                }
            }

            if(states[STATE_NONZERO]) {
                if(('0' <= c) & (c <= '9')) {
                    next[STATE_NONZERO] = 1;
                    next[STATE_SUFFIX] = 1;
                }
            }

            if(states[STATE_SUFFIX]) {
                if(c == suffix) {
                    next[STATE_ACCEPT] = 1;
                }
            }

            std::memcpy(states, next, sizeof(REState));
            if(next[STATE_ACCEPT]) {
                endidx = ii.getIndex();
            }

            ii.next();
        }

        if(endidx != std::numeric_limits<size_t>::max()) {
            this->advanceToken(ltoken, endidx - startidx);
            return true;
        }

        return false;
    }

    bool BSQONLexer::tryLexNat()
    {
        return this->lexIntegralHelper(false, 'n', BSQONTokenType::LiteralNat);
    }

    bool BSQONLexer::tryLexInt()
    {
        return this->lexIntegralHelper(true, 'i', BSQONTokenType::LiteralInt);
    }
    
    bool BSQONLexer::tryLexChkNat()
    {
        if(this->testchars(this->iter, "ChkNat::npos")) {
            this->advanceToken(BSQONTokenType::LiteralChkNat, strlen("ChkNat::npos") - 1);
            return true;
        }

        return this->lexIntegralHelper(false, 'N', BSQONTokenType::LiteralChkNat);
    }

    bool BSQONLexer::tryLexChkInt()
    {
        if(this->testchars(this->iter, "ChkInt::npos")) {
            this->advanceToken(BSQONTokenType::LiteralChkInt, strlen("ChkInt::npos") - 1);
            return true;
        }

        return this->lexIntegralHelper(true, 'I', BSQONTokenType::LiteralChkInt);
    }

    bool BSQONLexer::tryLexCString()
    {
        if(!this->iter.valid() || this->iter.get() != '\'') {
            return false;
        }

        std::list<uint8_t*>::const_iterator startbuff = this->iter.iobuffs;
        size_t startcindex = this->iter.cindex;
        size_t startidx = this->iter.gindex;

        this->iter.next(); //eat opening quote
        while(this->iter.valid() && this->iter.get() != '\'') {
            this->iter.next();
        }

        if(!this->iter.valid()) {
            this->ctoken = {BSQONTokenType::ErrorToken, startbuff, startcindex, startidx, this->iter.gindex - startidx};
        }
        else {
            this->iter.next(); //eat closing quote
            this->ctoken = {BSQONTokenType::LiteralCString, startbuff, startcindex, startidx, this->iter.gindex - startidx};
        }
        
        return true;
    }
        
    bool BSQONLexer::tryLexString()
    {
        if(!this->iter.valid() || this->iter.get() != '\"') {
            return false;
        }

        std::list<uint8_t*>::const_iterator startbuff = this->iter.iobuffs;
        size_t startcindex = this->iter.cindex;
        size_t startidx = this->iter.gindex;

        this->iter.next(); //eat opening quote
        while(this->iter.valid() && this->iter.get() != '\"') {
            this->iter.next();
        }

        if(!this->iter.valid()) {
            this->ctoken = {BSQONTokenType::ErrorToken, startbuff, startcindex, startidx, this->iter.gindex - startidx};
        }
        else {
            this->iter.next(); //eat closing quote
            this->ctoken = {BSQONTokenType::LiteralString, startbuff, startcindex, startidx, this->iter.gindex - startidx};
        }
        
        return true;
    }

    constexpr std::array<char, 8> s_symbol_tokens = { '(', ')', '{', '}', '[', ']', ',', '#' };
    bool BSQONLexer::tryLexSymbol()
    {
        if(!this->iter.valid() || (std::find(s_symbol_tokens.cbegin(), s_symbol_tokens.cend(), this->iter.get()) == s_symbol_tokens.cend())) {
            return false;
        }

        this->ctoken.tokentype = BSQONTokenType::LiteralSymbol;
        this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 1);
        return true;
    }

    constexpr std::array<const char*, 9> s_keyword_tokens = { };
    bool BSQONLexer::tryLexKeyword()
    {
        return false;
    }

    bool BSQONLexer::tryLexIdentifier()
    {
        auto ii = this->iter;
        bool badnest = false;
        while(ii.valid() && !badnest) {
            char c = (char)ii.get();
            bool ischar = (('a' <= c) & (c <= 'z')) || (('A' <= c) & (c <= 'Z')) || (c == '_');
            bool iscolon = (c == ':');
            bool isnum = ('0' <= c) & (c <= '9');

            if(ischar | ((isnum | iscolon) && ii.getIndex() != this->iter.getIndex())) {
                ii.next();
            }
            else {
                if(c != '<') {
                    break;
                }
                else {
                    //Handle generic type names by skipping to the matching '>'
                    size_t genericlevel = 1;
                    ii.next();
                    while(ii.valid() && genericlevel > 0) {
                        c = (char)ii.get();

                        if(c == '<') {
                            genericlevel++;
                        }
                        else if(c == '>') {
                            genericlevel--;
                        }
                        else {
                            bool ischarnested = (('a' <= c) & (c <= 'z')) || (('A' <= c) & (c <= 'Z')) || (c == '_');
                            bool iscolonnested = (c == ':');
                            bool isnumnested = ('0' <= c) & (c <= '9');
                            bool isoksym = (c == ',') || (c == ' ');

                            if(!(ischarnested | iscolonnested | isnumnested | isoksym)) {
                                break;
                            }
                        }
                        ii.next();
                    }

                    badnest = badnest || genericlevel != 0;
                }
            }
        }

        if(badnest || ii.getIndex() == this->iter.getIndex()) {
            return false;
        }
        
        this->ctoken.tokentype = BSQONTokenType::Identifier;
        this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, BSQONToken::sclongvalue, ii.getIndex() - this->iter.getIndex());
        return true;
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
        else if(this->tryLexCString() || this->tryLexString()) {
            return;
        }
        else if(this->tryLexSymbol() || this->tryLexKeyword() || this->tryLexIdentifier()) {
            return;
        }
        else {
            this->ctoken.tokentype = BSQONTokenType::ErrorToken;
            this->iter.advanceWithExtract(this->ctoken.startindex, this->ctoken.endindex, this->ctoken.scvalue, 1);
            return;
        }
    }
}

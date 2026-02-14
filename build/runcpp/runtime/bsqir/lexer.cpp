#include "lexer.h"

#include <regex>

namespace ᐸRuntimeᐳ
{
    static std::regex s_ws_re("^\\s+", std::regex_constants::nosubs | std::regex_constants::optimize);
    static std::regex s_line_comment_re("^%%[^\\n]*", std::regex_constants::nosubs | std::regex_constants::optimize);

    static std::regex s_nat_re("^(0|[+-]?[1-9][0-9]*)n", std::regex_constants::nosubs | std::regex_constants::optimize);
    static std::regex s_int_re("^(0|[+-]?[1-9][0-9]*)i", std::regex_constants::nosubs | std::regex_constants::optimize);
    static std::regex s_chknat_re("^(ChkNat::npos|((0|[+-]?[1-9][0-9]*)N))", std::regex_constants::nosubs | std::regex_constants::optimize);
    static std::regex s_chkint_re("^(ChkInt::npos|((0|[+-]?[1-9][0-9]*)I))", std::regex_constants::nosubs | std::regex_constants::optimize);

    constexpr std::array<char, 10> s_symbol_tokens = { '(', ')', '{', '}', '[', ']', '<', '>', ',', '#' };
    constexpr std::array<const char*, 6> s_keyword_tokens = { "none", "true", "false", "some", "ok", "fail" };

    static std::regex s_identifierlike_re("^([a-zA-Z_][a-zA-Z0-9_]*)", std::regex_constants::nosubs | std::regex_constants::optimize);

    bool BSQONToken::matches(const char* cchars) const
    {
        size_t len = std::strlen(cchars);
        if(len != this->size()) {
            return false;
        }

        return std::equal(this->begin, this->end, cchars);
    }
        
    void BSQONToken::extract(char* outchars, size_t maxlen) const
    {
        assert(maxlen > this->size());

        std::copy(this->begin, this->end, outchars);
        outchars[this->size()] = '\0';
    }

    void BSQONLexer::initialize(std::list<uint8_t*>&& iobuffs, size_t totalbytes)
    {
        this->iobuffs = std::move(iobuffs);
        this->iter = BSQLexBufferIterator::initializeBegin(this->iobuffs, totalbytes);
        this->iend = BSQLexBufferIterator::initializeEnd(this->iobuffs, totalbytes);
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
        this->iter = BSQLexBufferIterator::initializeBegin(this->iobuffs, 0);
        this->iend = BSQLexBufferIterator::initializeEnd(this->iobuffs, 0);
        this->ctoken.clear();
    }

    bool BSQONLexer::tryLexWS()
    {
        std::match_results<BSQLexBufferIterator> mm;
        if(!std::regex_search(this->iter, this->iend, mm, s_ws_re)) {
            return false;
        }

        std::advance(this->iter, mm[0].length());
        return true;
    }

    bool BSQONLexer::tryLexComment()
    {
        std::match_results<BSQLexBufferIterator> mm;
        if(!std::regex_search(this->iter, this->iend, mm, s_line_comment_re)) {
            return false;
        }

        std::advance(this->iter, mm[0].length());
        return true;
    }

    bool BSQONLexer::tryLexNat()
    {
        std::match_results<BSQLexBufferIterator> mm;
        if(!std::regex_search(this->iter, this->iend, mm, s_nat_re)) {
            return false;
        }

        this->advanceToken(BSQONTokenType::LiteralNat, mm[0].length());
        return true;
    }

    bool BSQONLexer::tryLexInt()
    {
        std::match_results<BSQLexBufferIterator> mm;
        if(!std::regex_search(this->iter, this->iend, mm, s_int_re)) {
            return false;
        }

        this->advanceToken(BSQONTokenType::LiteralInt, mm[0].length());
        return true;
    }
    
    bool BSQONLexer::tryLexChkNat()
    {
        std::match_results<BSQLexBufferIterator> mm;
        if(!std::regex_search(this->iter, this->iend, mm, s_chknat_re)) {
            return false;
        }

        this->advanceToken(BSQONTokenType::LiteralChkNat, mm[0].length());
        return true;
    }

    bool BSQONLexer::tryLexChkInt()
    {
        std::match_results<BSQLexBufferIterator> mm;
        if(!std::regex_search(this->iter, this->iend, mm, s_chkint_re)) {
            return false;
        }

        this->advanceToken(BSQONTokenType::LiteralChkInt, mm[0].length());
        return true;
    }

    bool BSQONLexer::tryLexCString()
    {
        if(*this->iter != '\'') {
            return false;
        }

        BSQLexBufferIterator istart = this->iter;

        ++this->iter; //eat opening quote
        BSQLexBufferIterator clquote = std::find(this->iter, this->iend, '\'');
        if(clquote == this->iend) {
            this->ctoken = {BSQONTokenType::ErrorToken, istart, this->iter};
        }
        else {
            ++clquote; //eat closing quote
            this->ctoken = {BSQONTokenType::LiteralCString, istart, clquote};
            this->iter = clquote;
        }
        
        return true;
    }
        
    bool BSQONLexer::tryLexString()
    {
        if(*this->iter != '\"') {
            return false;
        }

        BSQLexBufferIterator istart = this->iter;

        ++this->iter; //eat opening quote
        BSQLexBufferIterator clquote = std::find(this->iter, this->iend, '\"');
        if(clquote == this->iend) {
            this->ctoken = {BSQONTokenType::ErrorToken, istart, this->iter};
        }
        else {
            ++clquote; //eat closing quote
            this->ctoken = {BSQONTokenType::LiteralString, istart, clquote};
            this->iter = clquote;
        }
        
        return true;
    }

    bool BSQONLexer::tryLexSymbol()
    {
        if(std::find(s_symbol_tokens.cbegin(), s_symbol_tokens.cend(), *this->iter) == s_symbol_tokens.cend()) {
            return false;
        }

        this->advanceToken(BSQONTokenType::LiteralSymbol, 1);
        return true;
    }

    bool tryLexKeyword(const BSQLexBufferIterator& istart, const BSQLexBufferIterator& iend, size_t len)
    {
        auto ii = std::find_if(s_keyword_tokens.cbegin(), s_keyword_tokens.cend(), [istart, iend, len](const char* kw) {
           return std::strlen(kw) == len && std::equal(istart, iend, kw);
        });

        return ii != s_keyword_tokens.cend();
    }

    bool tryLexIdentifier(const BSQLexBufferIterator& istart, const BSQLexBufferIterator& iend, BSQLexBufferIterator& endout)
    {
        auto ii = istart;
        size_t idsize = 0;
        bool badnest = false;
        while(ii != iend && !badnest) {
            char c = *ii;
            idsize++;

            bool ischar = (('a' <= c) & (c <= 'z')) || (('A' <= c) & (c <= 'Z')) || (c == '_');
            bool iscolon = (c == ':');
            bool isnum = ('0' <= c) & (c <= '9');

            if(ischar | isnum | iscolon) {
                ++ii;
            }
            else {
                if(c != '<') {
                    break;
                }
                else {
                    //Handle generic type names by skipping to the matching '>'
                    size_t genericlevel = 1;
                    ++ii;
                    while(ii != iend && genericlevel > 0) {
                        c = *ii;
                        idsize++;

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
                        ++ii;
                    }

                    //we have bad nesting and hit the end of input so fail
                    if(genericlevel != 0) {
                        return false;
                    }

                    //Finished generic section -- break if the next token in not a : -- we dont want to consume something like Option<T>xyz
                    if((ii != iend && *ii != ':')) {
                        break;
                    }
                }
            }
        }

        endout = ii;
        return true;
    }

    bool BSQONLexer::tryLexIdentifierLike()
    {
        std::match_results<BSQLexBufferIterator> mm;
        if(!std::regex_search(this->iter, this->iend, mm, s_identifierlike_re)) {
            return false;
        }

        auto matchlen = mm[0].length();
        auto matchstriter = mm[0].first;
        auto matchstrenditer = mm[0].second;

        if(tryLexKeyword(matchstriter, matchstrenditer, matchlen)) {
            if(std::equal(matchstriter, matchstrenditer, "none")) {
                this->advanceToken(BSQONTokenType::LiteralNone, matchlen);
            }
            else if(std::equal(matchstriter, matchstrenditer, "true")) {
                this->advanceToken(BSQONTokenType::LiteralTrue, matchlen);
            }
            else if(std::equal(matchstriter, matchstrenditer, "false")) {
                this->advanceToken(BSQONTokenType::LiteralFalse, matchlen);
            }
            else {
                this->advanceToken(BSQONTokenType::LiteralKeyword, matchlen);
            }

            return true;
        }

        BSQLexBufferIterator outend;
        if(tryLexIdentifier(matchstriter, this->iend, outend)) {
            this->advanceToken(BSQONTokenType::Identifier, std::distance(this->iter, outend));
            return true;
        }

        return false;
    }


    void BSQONLexer::consume()
    {
        while((this->iter != this->iend) && (this->tryLexWS() || this->tryLexComment())) {
            ;
        }

        if(this->iter == this->iend) {
            this->ctoken.tokentype = BSQONTokenType::EOFToken;
            return;
        }

        if(this->tryLexNat() || this->tryLexInt() || this->tryLexChkNat() || this->tryLexChkInt()) {
            return;
        }
        else if(this->tryLexCString() || this->tryLexString()) {
            return;
        }
        else if(this->tryLexSymbol() || this->tryLexIdentifierLike()) {
            return;
        }
        else {
            this->advanceToken(BSQONTokenType::ErrorToken, 1);
            return;
        }
    }
}

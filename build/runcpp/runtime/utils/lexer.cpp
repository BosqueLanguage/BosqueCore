#include "lexer.h"

namespace ᐸRuntimeᐳ 
{
    constexpr auto s_regexflags = boost::regex_constants::ECMAScript | boost::regex_constants::nosubs | boost::regex_constants::optimize;

    static boost::regex s_ws_re("\\s+", s_regexflags);
    static boost::regex s_line_comment_re("%%[^\\n]*", s_regexflags);

    static boost::regex s_nat_re("(0|[+-]?[1-9][0-9]*)n", s_regexflags);
    static boost::regex s_int_re("(0|[+-]?[1-9][0-9]*)i", s_regexflags);
    static boost::regex s_chknat_re("(ChkNat::npos|((0|[+-]?[1-9][0-9]*)N))", s_regexflags);
    static boost::regex s_chkint_re("(ChkInt::npos|((0|[+-]?[1-9][0-9]*)I))", s_regexflags);

    //TODO: we kinda differ from fp repr in the Bosque langauge here -- at some point we probably want a fully unified format
    static boost::regex s_float_re("[+-]?(0|[1-9][0-9]*)(\\.[0-9]+)?([eE][+-]?[0-9]+)?f", s_regexflags);

    static boost::regex s_byte_re("0x[0-9a-fA-F]{1,2}", s_regexflags);
    static boost::regex s_cchar_re("c'[^']{1,16}'", s_regexflags);
    static boost::regex s_uchar_re("c\"[^\"]{1,16}\"", s_regexflags);

    static boost::regex s_bytebuffer_prefix_re("0x\\[", s_regexflags);
    static boost::regex s_bytebuffer_empty_re("0x\\[\\]", s_regexflags);
    
    static boost::regex s_symbol_re("[<>,{}#]|(=>)|(\\x28\\x7c?)|(\\x7c?\\x29)", s_regexflags);
                                    
    static boost::regex s_identifierlike_re("[a-zA-Z_][a-zA-Z0-9_:]*", s_regexflags);
    static boost::regex s_kwnone_re("none", s_regexflags);
    static boost::regex s_kwtrue_re("true", s_regexflags);
    static boost::regex s_kwfalse_re("false", s_regexflags);
    static boost::regex s_keyword_re("some|ok|fail", s_regexflags);

    static boost::regex s_constructor_equals_peek_re("\\s*=", s_regexflags);

    bool BAPILexer::tryLexWS()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_ws_re, boost::match_continuous)) {
            return false;
        }

        std::advance(this->iter, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexComment()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_line_comment_re, boost::match_continuous)) {
            return false;
        }

        std::advance(this->iter, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexNat()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_nat_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralNat, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexInt()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_int_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralInt, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexChkNat()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_chknat_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralChkNat, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexChkInt()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_chkint_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralChkInt, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexFloat()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_float_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralFloat, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexByte()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_byte_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralByte, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexCChar()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_cchar_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralCChar, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexUnicodeChar()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_uchar_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralUnicodeChar, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexCString()
    {
        if(*this->iter != '\'') {
            return false;
        }

        IOBufferIterator istart = this->iter;

        ++this->iter; //eat opening quote
        IOBufferIterator clquote = std::find(this->iter, this->end, '\'');
        if(clquote == this->end) {
            this->ctoken = {BAPITokenType::ErrorToken, istart, this->iter, (size_t)std::distance(istart, this->end)};
            this->iter = this->end;
        }
        else {
            ++clquote; //eat closing quote
            this->ctoken = {BAPITokenType::LiteralCString, istart, clquote, (size_t)std::distance(istart, clquote)};
            this->iter = clquote;
        }
        
        return true;
    }

    bool BAPILexer::tryLexString()
    {
        if(*this->iter != '"') {
            return false;
        }

        IOBufferIterator istart = this->iter;

        ++this->iter; //eat opening quote
        IOBufferIterator clquote = std::find(this->iter, this->end, '"');
        if(clquote == this->end) {
            this->ctoken = {BAPITokenType::ErrorToken, istart, this->iter, (size_t)std::distance(istart, this->end)};
            this->iter = this->end;
        }
        else {
            ++clquote; //eat closing quote
            this->ctoken = {BAPITokenType::LiteralString, istart, clquote, (size_t)std::distance(istart, clquote)};
            this->iter = clquote;
        }
        
        return true;
    }

    bool BAPILexer::tryLexByteBuffer()
    {
        boost::match_results<IOBufferIterator> mmprefix;
        if(!boost::regex_search(this->iter, this->end, mmprefix, s_bytebuffer_prefix_re, boost::match_continuous)) {
            return false;
        }

        boost::match_results<IOBufferIterator> mmempty;
        if(boost::regex_search(this->iter, this->end, mmempty, s_bytebuffer_empty_re, boost::match_continuous)) {
            this->advanceToken(BAPITokenType::LiteralByteBuffer, 4);
            return true;
        }
        else {
            IOBufferIterator istart = this->iter;
            std::advance(this->iter, 3); //eat opening 0x[

            IOBufferIterator clquote = std::find(this->iter, this->end, ']');
            if(clquote == this->end) {
                this->ctoken = {BAPITokenType::ErrorToken, istart, this->iter, (size_t)std::distance(istart, this->end)};
                this->iter = this->end;
            }
            else {
                ++clquote; //eat closing ]
                this->ctoken = {BAPITokenType::LiteralByteBuffer, istart, clquote, (size_t)std::distance(istart, clquote)};
                this->iter = clquote;
            }
            
            return true;
        }
    }

    bool BAPILexer::tryLexSymbol()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_symbol_re, boost::match_continuous)) {
            return false;
        }

        this->advanceToken(BAPITokenType::LiteralSymbol, mm[0].length());
        return true;
    }

    bool BAPILexer::tryLexIdentifierLike()
    {
        boost::match_results<IOBufferIterator> mm;
        if(!boost::regex_search(this->iter, this->end, mm, s_identifierlike_re, boost::match_continuous)) {
            return false;
        }

        if(boost::regex_match(mm[0].begin(), mm[0].end(), s_kwnone_re)) {
            this->advanceToken(BAPITokenType::LiteralNone, mm[0].length());
        }
        else if(boost::regex_match(mm[0].begin(), mm[0].end(), s_kwtrue_re)) {
            this->advanceToken(BAPITokenType::LiteralTrue, mm[0].length());
        }
        else if(boost::regex_match(mm[0].begin(), mm[0].end(), s_kwfalse_re)) {
            this->advanceToken(BAPITokenType::LiteralFalse, mm[0].length());
        }
        else if(boost::regex_match(mm[0].begin(), mm[0].end(), s_keyword_re)) {
            this->advanceToken(BAPITokenType::LiteralKeyword, mm[0].length());
        }
        else {
            auto iir = this->iter;
            std::advance(iir, mm[0].length()); //move to the token end

            if(iir == this->end || *iir != '<') {
                //nothing left or some regular character -- just an identifier thing
                this->advanceToken(BAPITokenType::Identifier, mm[0].length());
            }
            else {
                //template argument list follows -- we need to match nested parens and then loop eating any follow ::type::type things

                while(iir != this->end && *iir == '<') {
                    ++iir; //eat the opening <
                    size_t pcount = 1; //we have already seen the opening <

                    while((iir != this->end) && (pcount != 0)) {
                        if(*iir == '<') {
                            ++pcount;
                        }
                        if(*iir == '>') {
                            --pcount;
                        }

                        ++iir;
                    }

                    //we have matched a complete template argument list -- now continue to see if there are any trailing :: sequences
                    while((iir != this->end) && (*iir == ':')) {
                        ++iir;
                    }

                    //we have consumed any trailing :: sequences -- so parse another identifier if doable
                    if(boost::regex_search(iir, this->end, mm, s_identifierlike_re, boost::match_continuous)) {
                        std::advance(iir, mm[0].length());
                    }
                }

                this->advanceToken(BAPITokenType::Identifier, std::distance(this->iter, iir));
            }
        }

        return true;
    }

    void BAPILexer::initialize()
    {
        this->consume();
    }

    void BAPILexer::consume()
    {
        while((this->iter != this->end) && (this->tryLexWS() || this->tryLexComment())) {
            ;
        }

        if(this->iter == this->end) {
            this->ctoken.tokentype = BAPITokenType::EOFToken;
            return;
        }

        if(this->tryLexNat() || this->tryLexInt() || this->tryLexChkNat() || this->tryLexChkInt() || this->tryLexFloat()) {
            return;
        }
        else if(this->tryLexByte() || this->tryLexCChar() || this->tryLexUnicodeChar()) {
            return;
        }
        else if(this->tryLexCString() || this->tryLexString() || this->tryLexByteBuffer()) {
            return;
        }
        else if(this->tryLexSymbol() || this->tryLexIdentifierLike()) {
            return;
        }
        else {
            this->advanceToken(BAPITokenType::ErrorToken, 1);
            return;
        }
    }

    bool BAPILexer::equalPeekTest() const
    {
        return boost::regex_search(this->iter, this->end, s_constructor_equals_peek_re, boost::match_continuous);
    }
}

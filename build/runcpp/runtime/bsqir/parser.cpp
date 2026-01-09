#include "parser.h"

namespace ᐸRuntimeᐳ
{
    void BSQONParser::initialize(std::list<uint8_t*>&& iobuffs, size_t totalbytes)
    {
        this->lexer.initialize(std::move(iobuffs), totalbytes);
    }

    void BSQONParser::release()
    {
        this->lexer.release();
    }

    bool BSQONParser::peekSymbol(char sym)
    {
        auto token = this->lexer.current();
        if(token.tokentype != BSQONTokenType::LiteralSymbol) {
            return false;
        }

        return token.extract_single() == sym;
    }

    bool BSQONParser::ensureAndConsumeType(const char* tname)
    {
        auto token = this->lexer.current();
        if(!(token.tokentype == BSQONTokenType::Identifier)) {
            return false;
        }

        if(!this->lexer.current().matches(tname)) {
            return false;
        }

        this->lexer.consume();
        return true;
    }

    bool BSQONParser::ensureAndConsumeSymbol(char sym)
    {
        auto token = this->lexer.current();
        if(!(token.tokentype == BSQONTokenType::LiteralSymbol)) {
            return false;
        }

        if(token.extract_single() != sym) {
            return false;
        }

        this->lexer.consume();
        return true;
    }

    bool BSQONParser::ensureAndConsumeSymbol(const char* sym)
    {
        auto token = this->lexer.current();
        if(token.tokentype != BSQONTokenType::LiteralSymbol) {
            return false;
        }

        if(!this->lexer.current().matches(sym)) {
            return false;
        }

        this->lexer.consume();
        return true;
    }

    bool BSQONParser::ensureAndConsumeKeyword(const char* kw)
    {
        auto token = this->lexer.current();
        if(token.tokentype != BSQONTokenType::LiteralKeyword) {
            return false;
        }

        if(!this->lexer.current().matches(kw)) {
            return false;
        }

        this->lexer.consume();
        return true;
    }
    
    bool BSQONParser::ensureAndConsumeIdentifier(char* outid, size_t maxlen)
    {
        auto token = this->lexer.current();
        if(token.tokentype != BSQONTokenType::Identifier) {
            return false;
        }

        this->lexer.current().extract(outid, maxlen);
        
        this->lexer.consume();
        return true;
    }

    std::optional<XNone> BSQONParser::parseNone() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralNone) {
            this->lexer.consume();
            return std::optional<XNone>(none);
        }

        return std::nullopt;
    }

    
    std::optional<XBool> BSQONParser::parseBool() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralTrue) {
            this->lexer.consume();
            return std::optional<XBool>(TRUE);
        }
        else if(this->lexer.current().tokentype == BSQONTokenType::LiteralFalse) {
            this->lexer.consume();
            return std::optional<XBool>(FALSE);
        }

        return std::nullopt;
    }


    std::optional<XNat> BSQONParser::parseNat() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralNat) {
            char outbuff[32] = {0};
            this->lexer.current().extract(outbuff, 32);

            errno = 0;
            char* endptr = nullptr;
            int64_t vv = std::strtoll(outbuff, &endptr, 10);

            if(errno != 0 || endptr == outbuff || !XNat::isValidNat(vv)) {
                return std::nullopt;
            }
            else {
                this->lexer.consume();
                return std::optional<XNat>(XNat(vv));
            }
        }

        return std::nullopt;
    }

    std::optional<XInt> BSQONParser::parseInt() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralInt) {
            char outbuff[32] = {0};
            this->lexer.current().extract(outbuff, 32);

            errno = 0;
            char* endptr = nullptr;
            int64_t vv = std::strtoll(outbuff, &endptr, 10);

            if(errno != 0 || endptr == outbuff || !XInt::isValidInt(vv)) {
                return std::nullopt;
            }
            else {
                this->lexer.consume();
                return std::optional<XInt>(XInt(vv));
            }
        }

        return std::nullopt;
    }

    std::optional<XChkNat> BSQONParser::parseChkNat() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralChkNat) {
            char outbuff[64] = {0};
            this->lexer.current().extract(outbuff, 64);

            if(std::strcmp(outbuff, "ChkNat::npos") == 0) {
                this->lexer.consume();
                return std::optional<XChkNat>(XChkNat::bliteral());
            }
            else {
                errno = 0;
                char* endptr = nullptr;
                __int128_t vv = std::strtoll(outbuff, &endptr, 10);

                if(errno == ERANGE) {
                    assert(false); // Not Implemented: parsing very large ChkNat values
                }
                else if(endptr == outbuff || !XChkNat::isValidNat(vv)) {
                    return std::nullopt;
                }
                else {
                    this->lexer.consume();
                    return std::optional<XChkNat>(XChkNat(vv));
                }
            }
        }

        return std::nullopt;
    }

    std::optional<XChkInt> BSQONParser::parseChkInt() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralChkInt) {
            char outbuff[64] = {0};
            this->lexer.current().extract(outbuff, 64);

            if(std::strcmp(outbuff, "ChkInt::npos") == 0) {
                this->lexer.consume();
                return std::optional<XChkInt>(XChkInt::bliteral());
            }
            else {
                errno = 0;
                char* endptr = nullptr;
                __int128_t vv = std::strtoll(outbuff, &endptr, 10);

                if(errno == ERANGE) {
                    assert(false); // Not Implemented: parsing very large ChkNat values
                }
                else if(endptr == outbuff || !XChkInt::isValidInt(vv)) {
                    return std::nullopt;
                }
                else {
                    this->lexer.consume();
                    return std::optional<XChkInt>(XChkInt(vv));
                }
            }
        }

        return std::nullopt;
    }

    std::optional<XFloat> BSQONParser::parseFloat()
    {
        assert(false); // Not Implemented: parsing Float values
    }

    bool isSimpleChar(uint8_t c)
    {
        if(c > 126) {
            return false;
        }
        else {
            return std::isprint(c) || (c == '\t') || (c == '\n');
        }
    }

    bool processCCharInString(BSQLexBufferIterator& ii, char* outchar)
    {
        if(!ii.valid()) {
            return false;
        }

        char c = (char)ii.get();
        ii.next();

        if(!isSimpleChar(static_cast<uint8_t>(c))) {
            return false;
        }
        
        if(c != '%') {
            *outchar = c;
        }
        else {
            assert(false); // Not Implemented: escape sequences in CString
        }

        return true;
    }

    bool processUnicodeCharInString(BSQLexBufferIterator& ii, char32_t* outchar)
    {
        if(!ii.valid()) {
            return false;
        }

        char c = (char)ii.get();
        ii.next();

        if(!isSimpleChar(static_cast<uint8_t>(c))) {
            assert(false); // Not Implemented: full unicode support in String
        }
        else {
            if(c != '%') {
                *outchar = (char32_t)c;
            }
            else {
                assert(false); // Not Implemented: escape sequences in String
            }
        }

        return true;
    }

    std::optional<XCString> BSQONParser::parseCString()
    {
        if(this->lexer.current().tokentype != BSQONTokenType::LiteralCString) {
            return std::nullopt;
        }

        auto stok = this->lexer.current();
        if(stok.size < CStrBuff::CSTR_MAX_SIZE) {
            CStrBuff cb;
            size_t ecount = 0;
            bool extractok = true;
            BSQLexBufferIterator ii = stok.extraction_iterator();
            ii.next(); //eat ' and skip final '
            while(ii.valid() && ii.get() != '\'') {
                extractok &= processCCharInString(ii, &cb.data[ecount + 1]);
                ecount++;
            }
            cb.data[0] = static_cast<char>(ecount);

            this->lexer.consume();
            if(!extractok) {
                return std::nullopt;
            }
            else {
                return std::optional<XCString>(XCString(cb));
            }
        }
        else {
            assert(false); // Not Implemented: parsing large CString values
        }
    }

    std::optional<XString> BSQONParser::parseString()
    {
        if(this->lexer.current().tokentype != BSQONTokenType::LiteralString) {
            return std::nullopt;
        }

        auto stok = this->lexer.current();
        if(stok.size < StrBuff::STR_MAX_SIZE) {
            StrBuff cb;
            size_t ecount = 0;
            bool extractok = true;
            BSQLexBufferIterator ii = stok.extraction_iterator();
            ii.next(); //eat " and skip final "
            while(ii.valid() && ii.get() != '"') {
                extractok &= processUnicodeCharInString(ii, &cb.data[ecount + 1]);
                ecount++;
            }
            cb.data[0] = static_cast<char32_t>(ecount);

            this->lexer.consume();
            if(!extractok) {
                return std::nullopt;
            }
            else {
                return std::optional<XString>(XString(cb));
            }
        }
        else {
            assert(false); // Not Implemented: parsing large CString values
        }
    }
}
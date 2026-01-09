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

        if(!this->lexer.matches(tname)) {
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

        if(!this->lexer.matches(sym)) {
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

        if(!this->lexer.matches(kw)) {
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

        this->lexer.extract(outid, maxlen);
        
        this->lexer.consume();
        return;
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
            this->lexer.extract(outbuff, 32);

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
            this->lexer.extract(outbuff, 32);

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
            this->lexer.extract(outbuff, 64);

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
            this->lexer.extract(outbuff, 64);

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

    std::optional<XCString> BSQONParser::parseCString()
    {
        if(this->lexer.current().tokentype != BSQONTokenType::LiteralCString) {
            return std::nullopt;
        }

        if(this->lexer.current().size < CStrBuff::CSTR_MAX_SIZE) {
            char outbuff[CStrBuff::CSTR_BUFF_SIZE] = {0};
            this->lexer.extract(outbuff, CStrBuff::CSTR_BUFF_SIZE);

            CStrBuff cb;
            xxxx;

            this->lexer.consume();
            return std::optional<XCString>(XCString(cb));
        }
        else {
            assert(false); // Not Implemented: parsing large CString values
        }
    }

    std::optional<XString> BSQONParser::parseString()
    {
        assert(false); // Not Implemented: parsing String values
    }
}
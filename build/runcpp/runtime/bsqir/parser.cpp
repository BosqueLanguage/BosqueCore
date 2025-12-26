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
        if(!(token.tokentype == BSQONTokenType::LiteralSymbol)) {
            return false;
        }

        return token.scvalue[0] == sym;
    }

    bool BSQONParser::ensureAndConsumeType(const char* tname)
    {
        auto token = this->lexer.current();
        if(!(token.tokentype == BSQONTokenType::Identifier)) {
            return false;
        }

        if(std::strcmp(BSQONToken::sclongvalue, tname) != 0) {
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

        if(token.scvalue[0] != sym) {
            return false;
        }

        this->lexer.consume();
        return true;
    }

    bool BSQONParser::ensureAndConsumeSymbol(const char* sym)
    {
        auto token = this->lexer.current();
        if(!(token.tokentype == BSQONTokenType::LiteralSymbol)) {
            return false;
        }

        if(std::strcmp(token.scvalue, sym) != 0) {
            return false;
        }

        this->lexer.consume();
        return true;
    }

    bool BSQONParser::ensureAndConsumeKeyword(const char* kw)
    {
        auto token = this->lexer.current();
        if(!(token.tokentype == BSQONTokenType::LiteralKeyword)) {
            return false;
        }

        if(std::strcmp(token.scvalue, kw) != 0) {
            return false;
        }

        this->lexer.consume();
        return true;
    }
    
    void BSQONParser::ensureAndConsumeIdentifier(char* outid, size_t maxlen)
    {
        auto token = this->lexer.current();
        if(!(token.tokentype == BSQONTokenType::Identifier)) {
            return;
        }

        if(strlen(token.sclongvalue) >= maxlen) {
            return;
        }
        std::strncpy(outid, token.sclongvalue, maxlen);

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
            errno = 0;
            char* endptr = nullptr;
            int64_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

            if(errno != 0 || endptr == this->lexer.current().scvalue || !XNat::isValidNat(vv)) {
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
            errno = 0;
            char* endptr = nullptr;
            int64_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

            if(errno != 0 || endptr == this->lexer.current().scvalue || !XInt::isValidInt(vv)) {
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
            if(std::strcmp(this->lexer.current().scvalue, "ChkNat::npos") == 0) {
                this->lexer.consume();
                return std::optional<XChkNat>(XChkNat::bliteral());
            }
            else {
                errno = 0;
                char* endptr = nullptr;
                __int128_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

                if(errno != ERANGE) {
                    assert(false); // Not Implemented: parsing very large ChkNat values
                }
                else if(endptr == this->lexer.current().scvalue || !XChkNat::isValidNat(vv)) {
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
            if(std::strcmp(this->lexer.current().scvalue, "ChkInt::npos") == 0) {
                this->lexer.consume();
                return std::optional<XChkInt>(XChkInt::bliteral());
            }
            else {
                errno = 0;
                char* endptr = nullptr;
                __int128_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

                if(errno != ERANGE) {
                    assert(false); // Not Implemented: parsing very large ChkNat values
                }
                else if(endptr == this->lexer.current().scvalue || !XChkInt::isValidInt(vv)) {
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
        assert(false); // Not Implemented: parsing CString values
    }

    std::optional<XString> BSQONParser::parseString()
    {
        assert(false); // Not Implemented: parsing String values
    }
}
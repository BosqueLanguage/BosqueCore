#include "parser.h"

namespace ᐸRuntimeᐳ
{
    void BSQONParser::initialize(std::list<uint8_t*>&& iobuffs)
    {
        this->lexer.initialize(std::move(iobuffs));
    }

    void BSQONParser::release()
    {
        this->lexer.release();
    }

    std::optional<None> BSQONParser::parseNone() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralNone) {
            this->lexer.consume();
            return std::optional<None>(none);
        }

        return std::nullopt;
    }

    
    std::optional<Bool> BSQONParser::parseBool() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralTrue) {
            this->lexer.consume();
            return std::optional<Bool>(btrue);
        }
        else if(this->lexer.current().tokentype == BSQONTokenType::LiteralFalse) {
            this->lexer.consume();
            return std::optional<Bool>(bfalse);
        }

        return std::nullopt;
    }


    std::optional<Nat> BSQONParser::parseNat() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralNat) {
            errno = 0;
            char* endptr = nullptr;
            int64_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

            if(errno != 0 || endptr == this->lexer.current().scvalue || !Nat::isValidNat(vv)) {
                return std::nullopt;
            }
            else {
                this->lexer.consume();
                return std::optional<Nat>(Nat(vv));
            }
        }

        return std::nullopt;
    }

    std::optional<Int> BSQONParser::parseInt() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralInt) {
            errno = 0;
            char* endptr = nullptr;
            int64_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

            if(errno != 0 || endptr == this->lexer.current().scvalue || !Int::isValidInt(vv)) {
                return std::nullopt;
            }
            else {
                this->lexer.consume();
                return std::optional<Int>(Int(vv));
            }
        }

        return std::nullopt;
    }

    std::optional<ChkNat> BSQONParser::parseChkNat() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralChkNat) {
            if(this->lexer.current().scvalue[0] == '#') {
                this->lexer.consume();
                return std::optional<ChkNat>(ChkNat::bliteral());
            }
            else {
                errno = 0;
                char* endptr = nullptr;
                __int128_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

                if(errno != ERANGE) {
                    assert(false); // Not Implemented: parsing very large ChkNat values
                }
                else if(endptr == this->lexer.current().scvalue || !ChkNat::isValidNat(vv)) {
                    return std::nullopt;
                }
                else {
                    this->lexer.consume();
                    return std::optional<ChkNat>(ChkNat(vv));
                }
            }
        }

        return std::nullopt;
    }

    std::optional<ChkInt> BSQONParser::parseChkInt() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralChkInt) {
            if(this->lexer.current().scvalue[0] == '#') {
                this->lexer.consume();
                return std::optional<ChkInt>(ChkInt::bliteral());
            }
            else {
                errno = 0;
                char* endptr = nullptr;
                __int128_t vv = std::strtoll(this->lexer.current().scvalue, &endptr, 10);

                if(errno != ERANGE) {
                    assert(false); // Not Implemented: parsing very large ChkNat values
                }
                else if(endptr == this->lexer.current().scvalue || !ChkNat::isValidNat(vv)) {
                    return std::nullopt;
                }
                else {
                    this->lexer.consume();
                    return std::optional<ChkInt>(ChkInt(vv));
                }
            }
        }

        return std::nullopt;
    }
}
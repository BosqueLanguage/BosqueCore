#include "parser.h"

namespace ᐸRuntimeᐳ
{
    char* skipPlusSignOpt(char* ptr)
    {
        if(*ptr == '+') {
            return ptr + 1;
        }
        else {
            return ptr;
        }
    }

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

        return token.extract() == sym;
    }

    BSQONTokenType BSQONParser::peekTokenType()
    {
        return this->lexer.current().tokentype;
    }

    bool BSQONParser::testType(const char* tname)
    {
        auto token = this->lexer.current();
        if(!(token.tokentype == BSQONTokenType::Identifier)) {
            return false;
        }

        return this->lexer.current().matches(tname);
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
    
    bool BSQONParser::ensureAndConsumeIdentifier(char* outid, size_t maxlen)
    {
        auto token = this->lexer.current();
        if(token.tokentype != BSQONTokenType::Identifier) {
            return false;
        }

        bool isok = this->lexer.current().extract(outid, maxlen);
        
        this->lexer.consume();
        return isok;
    }

    void BSQONParser::consumeTokenAlways()
    {
        this->lexer.consume();
    }
    
    bool BSQONParser::testAndConsumeTokenIf(BSQONTokenType ttype)
    {
        auto token = this->lexer.current();
        if(token.tokentype != ttype) {
            return false;
        }

        this->lexer.consume();
        return true;
    }

    std::optional<XNone> BSQONParser::parseNone() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralNone) {
            this->lexer.consume();
            return std::make_optional(none);
        }

        return std::nullopt;
    }

    
    std::optional<XBool> BSQONParser::parseBool() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralTrue) {
            this->lexer.consume();
            return std::make_optional(TRUE);
        }
        else if(this->lexer.current().tokentype == BSQONTokenType::LiteralFalse) {
            this->lexer.consume();
            return std::make_optional(FALSE);
        }

        return std::nullopt;
    }


    std::optional<XNat> BSQONParser::parseNat() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralNat) {
            char outbuff[32] = {0};
            bool isok = this->lexer.current().extract(outbuff, sizeof(outbuff));
            if(!isok) {
                return std::nullopt;
            }

            int64_t vv = 0;
            auto [_, ec] = std::from_chars(skipPlusSignOpt(outbuff), outbuff + sizeof(outbuff), vv);

            if(ec != std::errc() || !XNat::isValidNat(vv)) {
                return std::nullopt;
            }
            else {
                this->lexer.consume();
                return std::make_optional(XNat{vv});
            }
        }

        return std::nullopt;
    }

    std::optional<XInt> BSQONParser::parseInt() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralInt) {
            char outbuff[32] = {0};
            bool isok = this->lexer.current().extract(outbuff, sizeof(outbuff));
            if(!isok) {
                return std::nullopt;
            }

            int64_t vv = 0;
            auto [_, ec] = std::from_chars(skipPlusSignOpt(outbuff), outbuff + sizeof(outbuff), vv);

            if(ec != std::errc() || !XInt::isValidInt(vv)) {
                return std::nullopt;
            }
            else {
                this->lexer.consume();
                return std::make_optional(XInt{vv});
            }
        }

        return std::nullopt;
    }

    std::optional<XChkNat> BSQONParser::parseChkNat() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralChkNat) {
            char outbuff[64] = {0};
            bool isok = this->lexer.current().extract(outbuff, sizeof(outbuff));
            if(!isok) {
                return std::nullopt;
            }

            if(std::strcmp(outbuff, "ChkNat::npos") == 0) {
                this->lexer.consume();
                return std::make_optional(XChkNat::bliteral());
            }
            else {

                __int128_t vv = 0;
                auto [_, ec] = std::from_chars(skipPlusSignOpt(outbuff), outbuff + sizeof(outbuff), vv);

                if(ec != std::errc() || !XChkNat::isValidNat(vv)) {
                    return std::nullopt;
                }
                else {
                    this->lexer.consume();
                    return std::make_optional(XChkNat{vv});
                }
            }
        }

        return std::nullopt;
    }

    std::optional<XChkInt> BSQONParser::parseChkInt() 
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralChkInt) {
            char outbuff[64] = {0};
            bool isok = this->lexer.current().extract(outbuff, sizeof(outbuff));
            if(!isok) {
                return std::nullopt;
            }

            if(std::strcmp(outbuff, "ChkInt::npos") == 0) {
                this->lexer.consume();
                return std::make_optional(XChkInt::bliteral());
            }
            else {

                __int128_t vv = 0;
                auto [_, ec] = std::from_chars(skipPlusSignOpt(outbuff), outbuff + sizeof(outbuff), vv);

                if(ec != std::errc() || !XChkInt::isValidInt(vv)) {
                    return std::nullopt;
                }
                else {
                    this->lexer.consume();
                    return std::make_optional(XChkInt{vv});
                }
            }
        }

        return std::nullopt;
    }

    std::optional<XFloat> BSQONParser::parseFloat()
    {
        if(this->lexer.current().tokentype == BSQONTokenType::LiteralFloat) {
            char outbuff[64] = {0};
            bool isok = this->lexer.current().extract(outbuff, sizeof(outbuff));
            if(!isok) {
                return std::nullopt;
            }

            double vv = 0;
            auto [_, ec] = std::from_chars(skipPlusSignOpt(outbuff), outbuff + sizeof(outbuff), vv);

            if(ec != std::errc() || !std::isfinite(vv)) {
                return std::nullopt;
            }
            else {
                this->lexer.consume();
                return std::make_optional(XFloat{vv});
            }
        }

        return std::nullopt;
    }

    bool extractEscapedSeq(BSQLexBufferIterator& ii, char closequote, std::array<char, 16>& outseq, size_t& outlen)
    {
        outseq.fill(0);
        outlen = 0;

        while(*ii != closequote && outlen < 16) {
            outseq[outlen] = *ii;
            ++ii;
            outlen++;

            if(outseq[outlen - 1] == ';') {
                return true;
            }
        }
        return false;
    }

    bool extractUTF8MultibyteSeq(BSQLexBufferIterator& ii, std::array<uint8_t, 6>& outseq, size_t& outlen)
    {
        outseq.fill(0);
        outlen = 0;

        //TODO: implement multibyte UFT8 decode
        assert(false);

        return false;
    }

    bool convertEscapedSeqToCChar(const std::array<char, 16>& outseq, size_t outlen, char& res)
    {
        res = 0;
        if(outlen < 2 || outseq[0] != '%' || outseq[outlen - 1] != ';') {
            return false;
        }

        auto ii = std::find_if(s_escape_names_char.cbegin(), s_escape_names_char.cend(), [&](const auto& p) { return std::strcmp(p.second, outseq.data()) == 0; });
        if(ii != s_escape_names_char.cend()) {
            res = (char)ii->first;
            return isLegalCChar(res);
        }

        if(outseq[1] == 'x') {
            uint8_t output = 0;
            auto [ptr, ec] = std::from_chars(outseq.data() + 2, outseq.data() + outlen - 1, output, 16);

            res = static_cast<char>(output);
            return ec == std::errc() && (ptr == outseq.data() + outlen - 1) && isLegalCChar(res);
        }

        return false;
    }

    bool convertEscapedSeqToUnicodeChar(const std::array<char, 16>& outseq, size_t outlen, char32_t& res)
    {
        res = 0;
        if(outlen < 2 || outseq[0] != '%' || outseq[outlen - 1] != ';') {
            return false;
        }

        if(outseq[1] == 'x') {
            uint32_t output = 0;
            auto [ptr, ec] = std::from_chars(outseq.data() + 2, outseq.data() + outlen - 1, output, 16);

            res = static_cast<char32_t>(output);
            return ec == std::errc() && (ptr == outseq.data() + outlen - 1) && isLegalUnicodeChar(res);
        }

        return false;
    }

    bool convertMultibyteSeqToUnicodeChar(const std::array<uint8_t, 6>& outseq, size_t outlen, char32_t& res)
    {
        res = 0;

        //TODO: implement multibyte UFT8 decode
        assert(false);

        return false;
    }

    bool processCCharFromIter(BSQLexBufferIterator& ii, char* outchar)
    {
        char c = *ii;
        
        if(c == '%') {
            std::array<char, 16> outseq;
            size_t outlen = 0;
            bool extractok = extractEscapedSeq(ii, '\'', outseq, outlen);
            if(!extractok) {
                return false;
            }

            char res = 0;
            bool convertok = convertEscapedSeqToCChar(outseq, outlen, res);
            if(!convertok) {
                return false;
            }

            *outchar = res;
            return isLegalCChar(*outchar);
        }
        else {
            if(c == '\'' || (c < 32) || (126 < c)) {
               return false;
            }
            else {
                *outchar = c;
                ++ii;

                return isLegalCChar(*outchar);
            }
        }
    }

    bool processUnicodeCharFromIter(BSQLexBufferIterator& ii, char32_t* outchar)
    {
        char c = *ii;
       
        if(c == '%') {
            std::array<char, 16> outseq;
            size_t outlen = 0;
            bool extractok = extractEscapedSeq(ii, '"', outseq, outlen);
            if(!extractok) {
                return false;
            }

            char32_t res = 0;
            bool convertok = convertEscapedSeqToUnicodeChar(outseq, outlen, res);
            if(!convertok) {
                return false;
            }

            *outchar = res;
            return isLegalUnicodeChar(*outchar);
        }
        else {
            if(c == '"') {
               return false;
            }
            else if(isMultibyteEncoding(c)) {
                std::array<uint8_t, 6> outseq;
                size_t outlen = 0;
                bool extractok = extractUTF8MultibyteSeq(ii, outseq, outlen);
                if(!extractok) {
                    return false;
                }

                char32_t res = 0;
                bool convertok = convertMultibyteSeqToUnicodeChar(outseq, outlen, res);
                if(!convertok) {
                    return false;
                }

                *outchar = res;
                return isLegalUnicodeChar(*outchar);
            }
            else {
                *outchar = static_cast<char32_t>(c);
                ++ii;

                return isLegalUnicodeChar(*outchar);
            }
        }
       

        return true;
    }

    std::optional<XByte> BSQONParser::parseByte()
    {
        if(this->lexer.current().tokentype != BSQONTokenType::LiteralByte) {
            return std::nullopt;
        }   

        auto stok = this->lexer.current();
        this->lexer.consume();

        char outbuff[16] = {0};
        stok.extract(outbuff, sizeof(outbuff));

        uint8_t output = 0;
        auto [ptr, ec] = std::from_chars(outbuff + 2, outbuff + stok.size(), output, 16);
        if(ec != std::errc() || (ptr != outbuff + stok.size())) {
            return std::nullopt;
        }

        return std::make_optional(XByte(output));
    }

    std::optional<XCChar> BSQONParser::parseCChar()
    {
        if(this->lexer.current().tokentype != BSQONTokenType::LiteralCChar) {
            return std::nullopt;
        }   

        auto stok = this->lexer.current();
        this->lexer.consume();

        BSQLexBufferIterator ii = stok.begin;
        ++ii; //eat 'c'
        ++ii; //eat '\''

        char output = 0;
        bool charok = processCCharFromIter(ii, &output);
        if(!charok || *ii != '\'') {
            return std::nullopt;
        }

        return std::make_optional(XCChar{static_cast<uint64_t>(output)});
    }

    std::optional<XUnicodeChar> BSQONParser::parseUnicodeChar()
    {
        if(this->lexer.current().tokentype != BSQONTokenType::LiteralUnicodeChar) {
            return std::nullopt;
        }   

        auto stok = this->lexer.current();
        this->lexer.consume();

        BSQLexBufferIterator ii = stok.begin;
        ++ii; //eat 'c'
        ++ii; //eat '"'

        char32_t output = 0;
        bool charok = processUnicodeCharFromIter(ii, &output);
        if(!charok || *ii != '"') {
            return std::nullopt;
        }

        return std::make_optional(XUnicodeChar{static_cast<uint64_t>(output)});
    }

    std::optional<XCString> BSQONParser::parseCString()
    {
        if(this->lexer.current().tokentype != BSQONTokenType::LiteralCString) {
            if(!this->sloppystrings || this->lexer.current().tokentype != BSQONTokenType::LiteralString) {
                return std::nullopt;
            }
        }

        char etok = '\'';
        if(this->sloppystrings && this->lexer.current().tokentype == BSQONTokenType::LiteralString) {
            etok = '"';
        }

        auto stok = this->lexer.current();
        if(stok.size() == 2) {
            this->lexer.consume();
            return std::make_optional(XCString());
        }
        else if(stok.size() - 2 <= CStrRootInlineContent::CSTR_MAX_SIZE) {
            CStrRootInlineContent cb;
            size_t ecount = 0;
            bool extractok = true;
            BSQLexBufferIterator ii = stok.begin;
            ++ii; //eat ' and skip final '
            while(*ii != etok) {
                extractok &= processCCharFromIter(ii, &cb.data[ecount + 1]);
                ecount++;
            }
            cb.data[0] = static_cast<char>(ecount);

            this->lexer.consume();
            if(!extractok) {
                return std::nullopt;
            }
            else {
                return std::make_optional(XCString(cb));
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
        if(stok.size() == 2) {
            this->lexer.consume();
            return std::make_optional(XString());
        }
        else if(stok.size() - 2 <= StrRootInlineContent::STR_MAX_SIZE) {
            StrRootInlineContent cb;
            size_t ecount = 0;
            bool extractok = true;
            BSQLexBufferIterator ii = stok.begin;
            ++ii; //eat " and skip final "
            while(*ii != '"') {
                extractok &= processUnicodeCharFromIter(ii, &cb.data[ecount + 1]);
                ecount++;
            }
            cb.data[0] = static_cast<char32_t>(ecount);

            this->lexer.consume();
            if(!extractok) {
                return std::nullopt;
            }
            else {
                return std::make_optional(XString(cb));
            }
        }
        else {
            assert(false); // Not Implemented: parsing large CString values
        }
    }

    std::optional<XCRegex> BSQONParser::parseCRegex()
    {
        assert(false); // Not Implemented: parsing CRegex values
    }

    std::optional<XRegex> BSQONParser::parseRegex()
    {
        assert(false); // Not Implemented: parsing Regex values
    }
}

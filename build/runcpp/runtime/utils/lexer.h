#pragma once

#include "../../common.h"

#include "builder.h"

namespace ᐸRuntimeᐳ 
{
    inline char* skipPlusSignOpt(char* ptr)
    {
        if(*ptr == '+') {
            return ptr + 1;
        }
        else {
            return ptr;
        }
    }

    enum class BAPITokenType : uint64_t
    {
        Invalid = 0,
        ErrorToken,
        EOFToken,
        LiteralNone,
        LiteralTrue,
        LiteralFalse,
        LiteralNat,
        LiteralInt,
        LiteralChkNat,
        LiteralChkInt,
        LiteralFloat,
        LiteralByte,
        LiteralCChar,
        LiteralUnicodeChar,
        LiteralCString,
        LiteralString,
        LiteralByteBuffer,
        LiteralSymbol,
        LiteralKeyword,
        Identifier
    };

    class BAPIToken
    {
    public:
        BAPITokenType tokentype;

        IOBufferIterator begin;
        IOBufferIterator end;
        
        size_t size;

        void clear()
        {
            this->tokentype = BAPITokenType::Invalid;
            this->size = 0;
        }

        bool matches(const uint8_t* data, size_t len) const
        {
            return (len == this->size) && std::equal(this->begin, this->end, data, data + len);
        }

        bool matchesID(const char* data) const
        {
            size_t idlen = strlen(data);
            return (idlen == this->size) && std::equal(this->begin, this->end, data, data + idlen);
        }

        uint8_t extract() const
        {
            return *this->begin;
        }

        size_t extract(std::array<uint8_t, 64>& outchars) const
        {
            assert(this->size < 64);

            std::copy(this->begin, this->end, outchars.begin());
            outchars[this->size] = 0;

            return this->size;
        }
    };

    class BAPILexer
    {
    private:
        IOBufferIterator iter;
        IOBufferIterator end;

        BAPIToken ctoken; //This is singleton and is re-used across lex calls

        void advanceToken(BAPITokenType tokentype, size_t len)
        {
            IOBufferIterator startiter = this->iter;
            std::advance(this->iter, len);

            this->ctoken = {tokentype, startiter, this->iter, len};
        }

        bool tryLexWS();
        bool tryLexComment();

        bool tryLexNat();
        bool tryLexInt();
        bool tryLexChkNat();
        bool tryLexChkInt();
        bool tryLexFloat();

        bool tryLexByte();
        bool tryLexCChar();
        bool tryLexUnicodeChar();

        bool tryLexCString();
        bool tryLexString();
        bool tryLexByteBuffer();

        bool tryLexSymbol();

        bool tryLexIdentifierLike();

        bool equalPeekTest() const;

    public:
        bool allowSloppyStrings;

        BAPILexer(IOBufferIterator iter, IOBufferIterator end, bool allowSloppyStrings): iter(iter), end(end), ctoken{BAPITokenType::Invalid, IOBufferIterator{}, IOBufferIterator{}, 0}, allowSloppyStrings(allowSloppyStrings) { ; }

        bool allInputConsumed()
        {
            while(this->tryLexWS() || this->tryLexComment())
            {
                ;// make sure to strip out any trailing whitespace or comments
            }

            return this->iter == this->end;
        }

        BAPITokenType getCurrentTokenType() const
        {
            return this->ctoken.tokentype;
        }

        size_t getCurrentTokenDataSize() const
        {
            return this->ctoken.size;
        }

        IOBufferIterator getCurrentTokenIterator() const
        {
            return this->ctoken.begin;
        }

        bool testDataMatches(const uint8_t* data, size_t len) const
        {
            return this->ctoken.matches(data, len);
        }

        bool testDataMatchesID(const char* data) const
        {
            return this->ctoken.matchesID(data);
        }
        
        bool constructorEqualsPeek() const
        {
            if(this->getCurrentTokenType() != BAPITokenType::Identifier) {
                return false;
            }

            return this->equalPeekTest();
        }

        uint8_t extractSingleCharToken() const
        {
            return this->ctoken.extract();
        }

        //also null terminate the output inbuffer
        size_t extractSmallToken(std::array<uint8_t, 64>& outchars) const
        {
            return this->ctoken.extract(outchars);
        }
        
        void initialize();
        
        void consume();

        bool testIsNone() const
        {
            return this->getCurrentTokenType() == BAPITokenType::LiteralNone;
        }

        bool testIsTrue() const
        {
            return this->getCurrentTokenType() == BAPITokenType::LiteralTrue;
        }

        bool testIsFalse() const
        {
            return this->getCurrentTokenType() == BAPITokenType::LiteralFalse;
        }

        bool testIsSymbol(char sym) const
        {
            auto tokentype = this->getCurrentTokenType();
            if(tokentype != BAPITokenType::LiteralSymbol || this->getCurrentTokenDataSize() != 1) {
                return false;
            }

            return this->extractSingleCharToken() == sym;
        }

        template<size_t N>
        bool testIsSymbol(const char (&sym)[N]) const
        {
            auto tokentype = this->getCurrentTokenType();
            if(tokentype != BAPITokenType::LiteralSymbol || this->getCurrentTokenDataSize() != N - 1) {
                return false;
            }

            return this->testDataMatches(reinterpret_cast<const uint8_t*>(sym), N - 1);
        }

        template<size_t N>
        bool testIsKeyword(const char (&sym)[N]) const
        {
            if(this->getCurrentTokenType() != BAPITokenType::LiteralKeyword || this->getCurrentTokenDataSize() != N - 1) {
                return false;
            }

            return this->testDataMatches(reinterpret_cast<const uint8_t*>(sym), N - 1);
        }

        bool testIsType(const char* tname) const
        {
            if(this->getCurrentTokenType() != BAPITokenType::Identifier) {
                return false;
            }

            return this->testDataMatchesID(tname);
        }

        template<typename T>
        bool tryExtractNumericValue(T& outval) const
        {
            std::array<uint8_t, 64> outchars;
            size_t size = this->extractSmallToken(outchars);

            auto [ptr, ec] = std::from_chars(skipPlusSignOpt(reinterpret_cast<char*>(outchars.data())), reinterpret_cast<char*>(outchars.data()) + size - 1, outval);
            return ec == std::errc() && ptr == reinterpret_cast<char*>(outchars.data()) + size - 1;
        }
    };
}
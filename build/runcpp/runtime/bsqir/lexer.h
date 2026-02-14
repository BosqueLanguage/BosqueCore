#pragma once

#include "../../common.h"
#include "../allocator/alloc.h"

namespace ᐸRuntimeᐳ
{
    class BSQLexBufferIterator
    {
    private:
        std::list<uint8_t*>::const_iterator iobuffs;
        int64_t cindex;

        int64_t gindex;
        int64_t totalbytes;

        BSQLexBufferIterator(std::list<uint8_t*>::const_iterator iobuffs, int64_t cindex, int64_t gindex, int64_t totalbytes) : iobuffs(iobuffs), cindex(cindex), gindex(gindex), totalbytes(totalbytes) {}

        void incrementSlow()
        {        
            this->iobuffs++;
            this->cindex = 0;
        }

        void decrementSlow()
        {        
            this->iobuffs--;
            this->cindex = MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE - 1;
        }

    public:
        using value_type = char;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        BSQLexBufferIterator() : iobuffs(), cindex(0), gindex(0), totalbytes(0) {}
        BSQLexBufferIterator(const BSQLexBufferIterator& other) = default;
        
        static BSQLexBufferIterator initializeBegin(const std::list<uint8_t*>& buff, size_t totalbytes)
        {
            return BSQLexBufferIterator(buff.cbegin(), 0, 0, totalbytes);
        }

        static BSQLexBufferIterator initializeEnd(const std::list<uint8_t*>& buff, size_t totalbytes)
        {
            return BSQLexBufferIterator(buff.cend(), 0, totalbytes, totalbytes);
        }

        value_type operator*() const 
        { 
            return (*this->iobuffs)[this->cindex]; 
        }

        BSQLexBufferIterator& operator++()
        {
            this->gindex++;
            this->cindex++;
            if(this->cindex >= (int64_t)MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE) {
                this->incrementSlow();
            }

            return *this;
        }
 
        BSQLexBufferIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        BSQLexBufferIterator& operator--()
        {
            this->gindex--;
            this->cindex--;
            if(this->cindex < 0) {
                this->decrementSlow();
            }

            return *this;
        }
 
        BSQLexBufferIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const BSQLexBufferIterator& lhs, const BSQLexBufferIterator& rhs)
        {
            return lhs.gindex == rhs.gindex;
        }

        friend bool operator!=(const BSQLexBufferIterator& lhs, const BSQLexBufferIterator& rhs) 
        {
            return lhs.gindex != rhs.gindex;
        }

        inline size_t getIndex() const 
        {
            return this->gindex;
        }
    };
    static_assert(std::bidirectional_iterator<BSQLexBufferIterator>);

    enum class BSQONTokenType : uint64_t
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
        LiteralCString,
        LiteralString,
        LiteralSymbol,
        LiteralKeyword,
        Identifier
    };

    class BSQONToken
    {
    public:
        BSQONTokenType tokentype;

        BSQLexBufferIterator begin;
        BSQLexBufferIterator end;

        void clear()
        {
            this->tokentype = BSQONTokenType::Invalid;
        }

        size_t size() const
        {
            return (size_t)(this->end.getIndex() - this->begin.getIndex());
        }

        uint8_t extract() const
        {
            return *(this->begin);
        }

        bool matches(const char* cchars) const;
        void extract(char* outchars, size_t maxlen) const;

        template<size_t len>
        bool xmatches(const char (&cchars)[len]) const
        {
            if((len - 1) != this->size()) {
                return false;
            }

            return std::equal(this->begin, this->end, cchars);
        }
    };

    class BSQONLexer
    {
    private:
        size_t totalbytes;

        std::list<uint8_t*> iobuffs;
        BSQLexBufferIterator iter;
        BSQLexBufferIterator iend;

        BSQONToken ctoken;

        void advanceToken(BSQONTokenType tokentype, size_t len)
        {
            BSQLexBufferIterator startiter = this->iter;
            std::advance(this->iter, len);

            this->ctoken = {tokentype, startiter, this->iter};
        }

        bool tryLexWS();
        bool tryLexComment();

        bool tryLexNat();
        bool tryLexInt();
        bool tryLexChkNat();
        bool tryLexChkInt();

        bool tryLexCString();
        bool tryLexString();

        bool tryLexSymbol();

        bool tryLexIdentifierLike();

    public:
        BSQONLexer() : totalbytes(0) {}

        void initialize(std::list<uint8_t*>&& iobuffs, size_t totalbytes);
        void release();

        const BSQONToken& current() const { return this->ctoken; }
        void consume();
    };
}

#pragma once

#include "../../common.h"
#include "../allocator/alloc.h"

namespace ᐸRuntimeᐳ
{
    class BSQLexBufferIterator
    {
    public:
        std::list<uint8_t*>::const_iterator iobuffs;
        size_t cindex;

        size_t gindex;
        size_t totalbytes;

        BSQLexBufferIterator() : iobuffs(), cindex(0), gindex(0), totalbytes(0) {}
        BSQLexBufferIterator(std::list<uint8_t*>::const_iterator iobuffs, size_t totalbytes) : iobuffs(iobuffs), cindex(0), gindex(0), totalbytes(totalbytes) {}
        BSQLexBufferIterator(std::list<uint8_t*>::const_iterator iobuffs, size_t cindex, size_t gindex, size_t totalbytes) : iobuffs(iobuffs), cindex(cindex), gindex(gindex), totalbytes(totalbytes) {}

        void reset()
        {
            this->cindex = 0;
            this->gindex = 0;
            this->totalbytes = totalbytes;
        }

        inline bool valid() const 
        {
            return (this->gindex < totalbytes);
        }

        inline uint8_t get() const 
        {
            return (*this->iobuffs)[this->cindex];
        }

        inline size_t getIndex() const 
        {
            return this->gindex;
        }

        void nextslow()
        {
            if(this->gindex < this->totalbytes) {
                this->iobuffs++;
                this->cindex = 0;            
            }
        }

        inline void next() 
        {
            this->gindex++;

            if(this->cindex + 1 < MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE) {
                this->cindex++;
            }
            else {
                this->nextslow();
            }
        }

        void advanceConstant(size_t len)
        {
            for(size_t i = 0; i < len; i++) {
                this->next();
            }
        }
    };

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

        std::list<uint8_t*>::const_iterator iobuff;
        size_t iobuffoffset;

        size_t startindex;
        size_t size;

        void clear()
        {
            this->tokentype = BSQONTokenType::Invalid;
        }

        uint8_t extract_single() const
        {
            return (*(this->iobuff))[this->iobuffoffset];
        }

        BSQLexBufferIterator extraction_iterator() const
        {
            return BSQLexBufferIterator(this->iobuff, this->iobuffoffset, this->startindex, this->startindex + this->size + 1);
        }

        bool matches(const char* cchars) const;
        void extract(char* outchars, size_t maxlen) const;

        template<size_t len>
        bool xmatches(const char (&cchars)[len]) const
        {
            if(len != this->size) {
                return false;
            }

            BSQLexBufferIterator ii = this->extraction_iterator();
            for(size_t i = 0; i < len; i++) {
                if(ii.get() != static_cast<uint8_t>(cchars[i])) {
                    return false;
                }
                ii.next();
            }

            return true;
        }
    };

    class BSQONLexer
    {
    private:
        size_t totalbytes;

        std::list<uint8_t*> iobuffs;
        BSQLexBufferIterator iter;

        BSQONToken ctoken;

        static bool testchar(const BSQLexBufferIterator& ii, char c);
        static bool testchars(BSQLexBufferIterator ii, const char* chars);

        void advanceToken(BSQONTokenType tokentype, size_t len)
        {
            this->ctoken = {tokentype, this->iter.iobuffs, this->iter.cindex, this->iter.gindex, len};
            this->iter.advanceConstant(len);
        }

        bool tryLexNone();
        bool tryLexBool();

        bool lexIntegralHelper(bool negok, char suffix, BSQONTokenType ltoken);
        bool tryLexNat();
        bool tryLexInt();
        bool tryLexChkNat();
        bool tryLexChkInt();

        bool tryLexCString();
        bool tryLexString();

        bool tryLexSymbol();
        bool tryLexKeyword();
        bool tryLexIdentifier();

    public:
        BSQONLexer() : totalbytes(0) {}

        void initialize(std::list<uint8_t*>&& iobuffs, size_t totalbytes);
        void release();

        const BSQONToken& current() const { return this->ctoken; }
        void consume();
    };
}

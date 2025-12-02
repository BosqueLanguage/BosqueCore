#pragma once

#include "../../common.h"
#include "../allocator/alloc.h"

namespace ᐸRuntimeᐳ
{
    class BSQLexBufferIterator
    {
    private:
        std::list<uint8_t*>::const_iterator iobuffs;
        uint8_t* centry;
        size_t cindex;

        size_t gindex;
        size_t totalbytes;

    public:
        void initialize(std::list<uint8_t*>::const_iterator iobuffs, size_t totalbytes) 
        { 
            this->iobuffs = iobuffs;
            this->centry = *iobuffs;
            this->cindex = 0;
            this->gindex = 0;
            this->totalbytes = totalbytes;
        }

        void clear(std::list<uint8_t*>::const_iterator iobuffs)
        {
            this->iobuffs = iobuffs;
            this->centry = nullptr;
            this->cindex = 0;
            this->gindex = 0;
            this->totalbytes = 0;
        }

        inline bool valid() const 
        {
            return (this->gindex < totalbytes);
        }

        inline uint8_t get() const 
        {
            return this->centry[this->cindex];
        }

        inline size_t getIndex() const 
        {
            return this->gindex;
        }

        void nextslow()
        {
            if(this->gindex < this->totalbytes) {
                this->iobuffs++;
                this->centry = *this->iobuffs;
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

        inline void advance(size_t& startidx, size_t& endidx, size_t count)
        {
            startidx = this->gindex;
            endidx = startidx + count;
            for(size_t i = 0; i < count; i++) {
                this->next();
            }
        }

        inline void advanceWithExtract(size_t& startidx, size_t& endidx, char* outbuf, size_t count)
        {
            startidx = this->gindex;
            endidx = startidx + count;
            for(size_t i = 0; i < count; i++) {
                outbuf[i] = (char)this->get();
                this->next();
            }
            outbuf[count] = '\0';
        }
    };

    enum class BSQONTokenType
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
        LiteralChkInt
    };

    class BSQONToken
    {
    public:
        BSQONTokenType tokentype;
        size_t startindex;
        size_t endindex;

        char scvalue[32]; // Simple constant value storage for small literals (bool, nat, int, uuidv4)

        BSQONToken() : tokentype(BSQONTokenType::Invalid), startindex(0), endindex(0), scvalue{0} {}
        BSQONToken(const BSQONToken& other) = default;

        void clear()
        {
            this->tokentype = BSQONTokenType::Invalid;
            this->startindex = 0;
            this->endindex = 0;
            std::memset(this->scvalue, 0, sizeof(this->scvalue));
        }
    };

    class BSQONLexer
    {
    private:
        std::list<uint8_t*> iobuffs;
        BSQLexBufferIterator iter;

        BSQONToken ctoken;

        static bool testchar(const BSQLexBufferIterator& ii, char c);
        static bool testchars(BSQLexBufferIterator ii, const char* chars);

        bool tryLexNone();
        bool tryLexBool();

        bool lexIntegralHelper(bool negok, char suffix);
        bool tryLexNat();
        bool tryLexInt();
        bool tryLexChkNat();
        bool tryLexChkInt();

    public:
        BSQONLexer() : iobuffs(), iter(), ctoken() {}

        void initialize(std::list<uint8_t*>&& iobuffs);
        void release();

        const BSQONToken& current() const { return this->ctoken; }
        void consume();
    };
}

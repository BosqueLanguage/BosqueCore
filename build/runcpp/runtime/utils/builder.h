#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ 
{
    std::string getDisplayIndent(std::optional<std::string> indent);
    
    /* This is an abstract class for streaming bytes/char/char32 values into a some BSQ object (or byte stream) that can buffer and build efficiently from the input data */   
    class BSQStreamingBuilder
    {
    public:
        BSQStreamingBuilder() {}

        virtual void appendByte(uint8_t byte) = 0;

        virtual void appendChar(char c) = 0;
        virtual void appendChar(char32_t cchar) = 0;

        virtual void appendConstString(const char* str, size_t len) = 0;
        virtual void appendConstString(const char* str) = 0;

        template<size_t N>
        void appendLiteralString(const char(&str)[N])
        {
            appendConstString(str, N - 1);
        }
    };

    class IOBufferStreamingBuilder : public BSQStreamingBuilder
    {
    public:
        uint8_t* cpos;
        uint8_t* epos;

        size_t totalbytes;
        std::list<uint8_t*> iobuffs;

        bool allowsensitive;

        IOBufferStreamingBuilder(bool allowsensitive) : cpos(nullptr), epos(nullptr), totalbytes(0), iobuffs{}, allowsensitive(allowsensitive) {}

        void rotateData();
        void writeSlow(uint8_t c);
        void writeSlowTail(const char* str, size_t slen);

        void appendByte(uint8_t c) override
        {
            if(this->cpos == this->epos) [[unlikely]] {
                this->writeSlow(c);
            }
            else {
                *(this->cpos) = (uint8_t)c;
                this->cpos++;
                this->totalbytes++;
            }
        }

        void appendChar(char c) override
        {
            if(this->cpos == this->epos) [[unlikely]] {
                this->writeSlow(c);
            }
            else {
                *(this->cpos) = (uint8_t)c;
                this->cpos++;
                this->totalbytes++;
            }
        }

        void appendChar(char32_t cchar) override
        {
            assert(false); //This is not supported for streaming bytebuffer builders
        }

        void appendConstString(const char* str, size_t slen) 
        {
            if(this->cpos == this->epos) [[unlikely]] {
                this->rotateData();
            }

            size_t initcopylen = std::min((size_t)(this->epos - this->cpos), slen);

            std::memcpy(this->cpos, str, initcopylen);
            this->cpos += initcopylen;
            this->totalbytes += initcopylen;

            if(initcopylen != slen) [[unlikely]] {
                this->writeSlowTail(str + initcopylen, slen - initcopylen);
            }
        }

        void appendConstString(const char* str) {
            this->appendConstString(str, std::strlen(str));
        }

        size_t finalize(std::list<uint8_t*>& iobuffs)
        {
            this->cpos = nullptr;
            this->epos = nullptr;

            iobuffs = std::move(this->iobuffs);
            return this->totalbytes;
        }
    };
}

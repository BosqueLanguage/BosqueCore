#pragma once

#include "../../common.h"
#include "../allocator/bsqalloc.h"

namespace ᐸRuntimeᐳ
{
    class BSQEmitBufferMgr
    {
    private:
        uint8_t* cpos;
        uint8_t* epos;

        size_t bytes;
        size_t indentlevel; 
        std::list<BSQIOBuffer> buffers;

    public:
        BSQEmitBufferMgr() : cpos(nullptr), epos(nullptr), bytes(0), indentlevel(0) {}

        void prepForEmit();
        
        void increaseIndent() {
            this->indentlevel++;
        }

        void decreaseIndent() {
            this->indentlevel--;
        }
        
        void write(char c) {
            if(this->cpos == this->epos) {
                BSQIOBuffer newbuf = xxxx; //CALL ALLOCATOR HERE TO GET A NEW BUFFER
                this->buffers.push_back(newbuf);

                this->cpos = newbuf;
                this->epos = newbuf + BSQ_BUFFER_ALLOCATOR_BLOCK_SIZE;
            }

            *(this->cpos) = (uint8_t)c;
            this->cpos++;
            this->bytes++;
        }

        void write(const char* str) {
            size_t slen = strlen(str);
            size_t okcpylen = std::min((size_t)(this->epos - this->cpos), slen);

            std::memcpy(this->cpos, str, okcpylen);
            this->cpos += okcpylen;
            this->bytes += okcpylen;

            size_t remlen = slen - okcpylen;
            if(remlen > 0) {
                xxxx;
            }
        }

        void writef(const char* fmt, ...);

        void writeIndent() {
            for(size_t i = 0; i < this->indentlevel; i++) {
                this->write(' ');
                this->write(' ');
            }
        }

        void writeNewline() {
            this->write('\n');
        }

        std::list<BSQIOBuffer> completeEmit();
    };

    class BSQONEmitter
    {

    };

    class JSONEmitter
    {

    };
}


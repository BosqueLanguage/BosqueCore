#pragma once

#include "../../common.h"
#include "../allocator/alloc.h"

#include "../../core/coredecls.h"

#include "../../core/bools.h"
#include "../../core/chars.h"
#include "../../core/integrals.h"
#include "../../core/strings.h"
#include "../../core/bytebuff.h"

namespace ᐸRuntimeᐳ
{
    /**
     * A buffer manager for emitting BSQON or other text formats (e.g. JSON). This should be local per thread.
     */
    class BSQEmitBufferMgr
    {
    private:
        uint8_t* cpos;
        uint8_t* epos;

        size_t bytes;
        size_t maxbytes;
        size_t indentlevel; 

        uint8_t* cdata;

        std::list<uint8_t*> iobuffs;

    public:
        BSQEmitBufferMgr() : cpos(nullptr), epos(nullptr), bytes(0), maxbytes(0), indentlevel(0), cdata(nullptr), iobuffs() { }

        void prepForEmit();
        
        void increaseIndent() 
        {
            this->indentlevel++;
        }

        void decreaseIndent() 
        {
            this->indentlevel--;
        }
        
        void rotateData();
        void writeSlow(char c);
        void writeSlowTail(const char* str, size_t slen);

        void write(char c)
        {
            if(this->cpos == this->epos) [[unlikely]] {
                this->writeSlow(c);
            }
            else {
                *(this->cpos) = (uint8_t)c;
                this->cpos++;
                this->bytes++;
            }
        }

        void write(const char* str, size_t slen) 
        {
            size_t initcopylen = std::min((size_t)(this->epos - this->cpos), slen);

            std::memcpy(this->cpos, str, initcopylen);
            this->cpos += initcopylen;
            this->bytes += initcopylen;

            if(initcopylen != slen) [[unlikely]] {
                this->writeSlowTail(str + initcopylen, slen - initcopylen);
            }
        }

        void write(const char* str) {
            this->write(str, std::strlen(str));
        }

        template<size_t len>
        void writeImmediate(const char (&cstr)[len])
        {
            if constexpr (len - 1 == 0) {
                return;
            }
            else {
                if constexpr (len - 1 == 1) {
                    this->write(cstr[0]);
                }
                else {
                    if(len - 1 <= (size_t)(this->epos - this->cpos)) {
                        std::memcpy(this->cpos, cstr, len - 1);
                        this->cpos += (len - 1);
                        this->bytes += (len - 1);
                    }
                    else {
                        this->write(cstr, len - 1);
                    }
                }
            }
        }

        template <typename T>
        void writeNumberWFormat(const char* fmt, const T& val)
        {
            char numbuf[64];
            int written = std::snprintf(numbuf, sizeof(numbuf), fmt, val);
            this->write(numbuf, static_cast<size_t>(written));
        }

        void writeIndent()
        {
            for(size_t i = 0; i < this->indentlevel; i++) {
                this->writeImmediate("  ");
            }
        }

        void writeNewline() 
        {
            this->write('\n');
        }

        std::list<uint8_t*>&& completeEmit(size_t& bytes);
    };

    class BSQONEmitter
    {
    private:
        BSQEmitBufferMgr bufferMgr;

        bool sensitiveOutputEnabled;

    public:
        BSQONEmitter() : bufferMgr(), sensitiveOutputEnabled(true) {}

        void prepForEmit(bool sensitive) 
        { 
            this->sensitiveOutputEnabled = sensitive;
            this->bufferMgr.prepForEmit(); 
        }

        void emitLiteralContent(const char* lit)
        {
            this->bufferMgr.write(lit);
        }

        void emitSymbol(char sym)
        {
            this->bufferMgr.write(sym);
        }

        template<size_t len>
        void writeImmediate(const char (&cstr)[len])
        {
            this->bufferMgr.writeImmediate(cstr);
        }

        void emitNone(XNone n);
        void emitBool(XBool b);
        void emitNat(XNat n);
        void emitInt(XInt i);
        void emitChkNat(XChkNat n);
        void emitChkInt(XChkInt i);

        void emitFloat(XFloat f);

        //
        //Lots more here
        //

        void emitByte(XByte b);
        void emitCChar(XCChar c);
        void emitUnicodeChar(XUnicodeChar c);

        void emitCString(XCString s);
        void emitString(XString s);

        //
        //Lots more here
        //

        std::list<uint8_t*>&& completeEmit(size_t& bytes);
    };

    class JSONEmitter
    {

    };
}


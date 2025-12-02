#pragma once

#include "../../common.h"
#include "../allocator/alloc.h"

#include "../../core/bools.h"
#include "../../core/chars.h"
#include "../../core/integrals.h"
#include "../../core/strings.h"
#include "../../core/bytebuff.h"

namespace ᐸRuntimeᐳ
{
    /**
     * A buffer manager for emitting BSQON or other text formats (e.g. JSON). This should be local per thread. The buffers may be IO or GC allocated depending on the output target.
     */
    class BSQEmitBufferMgr
    {
    private:
        uint8_t* cpos;
        uint8_t* epos;

        size_t bytes;
        size_t indentlevel; 

        ByteBufferBlock* buffs;
        uint8_t data[ByteBufferEntry::BUFFER_ENTRY_SIZE];

        bool isIOEmit; //whether this is an IO emit (vs GC emit) -- determines allocator used and GC root processing

    public:
        BSQEmitBufferMgr() : cpos(nullptr), epos(nullptr), bytes(0), indentlevel(0) {}

        void prepForEmit(bool isIOEmit);
        
        void increaseIndent() 
        {
            this->indentlevel++;
        }

        void decreaseIndent() 
        {
            this->indentlevel--;
        }
        
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
            char numbuf[32];
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

        std::list<ByteBufferBlock>&& completeEmit(size_t& bytes);
    };

    class BSQONEmitter
    {
    private:
        BSQEmitBufferMgr bufferMgr;

        bool sensitiveOutputEnabled;

    public:
        BSQONEmitter(bool sensitiveEnabled) : bufferMgr(), sensitiveOutputEnabled(sensitiveEnabled) {}

        void emitNone();
        void emitBool(Bool b);
        void emitNat(Nat n);
        void emitInt(Int i);
        void emitChkNat(ChkNat n);
        void emitChkInt(ChkInt i);

        void emitRational();
        void emitFloat();

        //
        //Lots more here
        //

        void emitByte(Byte b);
        void emitCChar(CChar c);
        void emitUnicodeChar(UnicodeChar c);

        void emitCString(CString s);
        void emitString(String s);

        //
        //Lots more here
        //
    };

    class JSONEmitter
    {

    };
}


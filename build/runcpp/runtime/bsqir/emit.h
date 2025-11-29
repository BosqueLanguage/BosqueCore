#pragma once

#include "../../common.h"
#include "../allocator/bsqalloc.h"

#include "../../core/bools.h"
#include "../../core/chars.h"
#include "../../core/integrals.h"
#include "../../core/strings.h"

namespace ᐸRuntimeᐳ
{
    /**
     * A buffer manager for emitting BSQON or other text formats (e.g. JSON). This should be 1 per thread (and thread local). We depend on the underlying allocator for fetching new buffers.
     * This needs to be coordinated with the allocator and host to ensure proper buffer sizes and deallocation.
     */
    class BSQEmitBufferMgr
    {
    private:
        uint8_t* cpos;
        uint8_t* epos;

        size_t bytes;
        size_t indentlevel; 
        std::list<BSQIOBuffer> buffers;

    public:
        BSQEmitBufferMgr() noexcept : cpos(nullptr), epos(nullptr), bytes(0), indentlevel(0) {}

        void prepForEmit() noexcept;
        
        void increaseIndent() noexcept 
        {
            this->indentlevel++;
        }

        void decreaseIndent() noexcept 
        {
            this->indentlevel--;
        }
        
        void writeSlow(char c) noexcept;
        void writeSlowTail(const char* str, size_t slen) noexcept;

        void write(char c) noexcept
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

        void write(const char* str, size_t slen) noexcept 
        {
            size_t initcopylen = std::min((size_t)(this->epos - this->cpos), slen);

            std::memcpy(this->cpos, str, initcopylen);
            this->cpos += initcopylen;
            this->bytes += initcopylen;

            if(initcopylen != slen) [[unlikely]] {
                this->writeSlowTail(str + initcopylen, slen - initcopylen);
            }
        }

        void write(const char* str) noexcept {
            this->write(str, std::strlen(str));
        }

        template<size_t len>
        void writeImmediate(const char (&cstr)[len]) noexcept
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
        void writeNumberWFormat(const char* fmt, const T& val) noexcept
        {
            char numbuf[32];
            int written = std::snprintf(numbuf, sizeof(numbuf), fmt, val);
            this->write(numbuf, static_cast<size_t>(written));
        }

        void writeIndent() noexcept
        {
            for(size_t i = 0; i < this->indentlevel; i++) {
                this->writeImmediate("  ");
            }
        }

        void writeNewline() noexcept 
        {
            this->write('\n');
        }

        std::list<BSQIOBuffer>&& completeEmit(size_t& bytes) noexcept;
    };

    class BSQONEmitter
    {
    private:
        BSQEmitBufferMgr bufferMgr;

        bool sensitiveOutputEnabled;

    public:
        BSQONEmitter(bool sensitiveEnabled) noexcept : bufferMgr(), sensitiveOutputEnabled(sensitiveEnabled) {}

        void emitNone() noexcept;
        void emitBool(Bool b) noexcept;
        void emitNat(Nat n) noexcept;
        void emitInt(Int i) noexcept;
        void emitChkNat(ChkNat n) noexcept;
        void emitChkInt(ChkInt i) noexcept;

        void emitRational() noexcept;
        void emitFloat() noexcept;

        //
        //Lots more here
        //

        void emitByte(Byte b) noexcept;
        void emitCChar(CChar c) noexcept;
        void emitUnicodeChar(UnicodeChar c) noexcept;

        void emitCString(CString s) noexcept;
        void emitString(String s) noexcept;

        //
        //Lots more here
        //
    };

    class JSONEmitter
    {

    };
}


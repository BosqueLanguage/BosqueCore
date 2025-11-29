#include "emit.h"


namespace ᐸRuntimeᐳ
{
    void BSQEmitBufferMgr::prepForEmit() noexcept
    {
        this->cpos = nullptr;
        this->epos = nullptr;
        this->bytes = 0;
        this->indentlevel = 0;
        this->buffers.clear();
    }
        
    void BSQEmitBufferMgr::writeSlow(char c) noexcept
    {
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

    void BSQEmitBufferMgr::writeSlowTail(const char* str, size_t slen) noexcept
    {
        BSQIOBuffer newbuf = xxxx; //CALL ALLOCATOR HERE TO GET A NEW BUFFER
        this->buffers.push_back(newbuf);

        this->cpos = newbuf;
        this->epos = newbuf + BSQ_BUFFER_ALLOCATOR_BLOCK_SIZE;

        std::memcpy(this->cpos, str, slen);
        this->cpos += slen;
        this->bytes += slen;
    }
        
    std::list<BSQIOBuffer>&& BSQEmitBufferMgr::completeEmit(size_t& bytes) noexcept
    {
        this->cpos = nullptr;
        this->epos = nullptr;
        this->indentlevel = 0;

        bytes = this->bytes;
        this->bytes = 0;

        return std::move(this->buffers);
    }

    void BSQONEmitter::emitNone() noexcept
    {
        this->bufferMgr.writeImmediate("none");
    }

    void BSQONEmitter::emitBool(Bool b) noexcept
    {
        if(Bool::toBool(b)) {
            this->bufferMgr.writeImmediate("true");
        }
        else {
            this->bufferMgr.writeImmediate("false");
        }
    }
        
    void BSQONEmitter::emitNat(Nat n) noexcept
    {
        this->bufferMgr.writeNumberWFormat("%llin", n.getValue());
    }

    void BSQONEmitter::emitInt(Int i) noexcept
    {
        this->bufferMgr.writeNumberWFormat("%llin", i.getValue());
    }

    void BSQONEmitter::emitChkNat(ChkNat n) noexcept
    {
        if(n.isBottom()) {
            this->bufferMgr.writeImmediate("#");
        }
        else {
            if(n.getValue() <= (__int128_t)std::numeric_limits<int64_t>::max()) {
                this->bufferMgr.writeImmediate("overflow");
            }
            else {
                assert(false); // Not Implemented: format for very large ChkNat values
            }
        }
    }

    void BSQONEmitter::emitChkInt(ChkInt i) noexcept
    {
        if(i.isBottom()) {
            this->bufferMgr.writeImmediate("#");
        }
        else {
            if(((__int128_t)std::numeric_limits<int64_t>::min() <= i.getValue()) & (i.getValue() <= (__int128_t)std::numeric_limits<int64_t>::max())) {
                this->bufferMgr.writeNumberWFormat("%llin", static_cast<int64_t>(i.getValue()));
            }
            else {
                assert(false); // Not Implemented: format for very large ChkInt values
            }
        }
    }

    void BSQONEmitter::emitByte(Byte b) noexcept
    {
        this->bufferMgr.writeNumberWFormat("0x%x", b.getValue());
    }

    void BSQONEmitter::emitCChar(CChar c) noexcept
    {
        xxxx;
    }

    void BSQONEmitter::emitUnicodeChar(UnicodeChar c) noexcept
    {
        assert(false); // Not Implemented
    }

    void BSQONEmitter::emitCString(CString s) noexcept
    {
        xxxx;
    }

    void BSQONEmitter::emitString(String s) noexcept
    {
        assert(false); // Not Implemented
    }
}
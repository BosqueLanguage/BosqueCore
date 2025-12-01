#include "emit.h"

namespace ᐸRuntimeᐳ
{
    void BSQEmitBufferMgr::prepForEmit(bool isIOEmit)
    {
        this->cpos = nullptr;
        this->epos = nullptr;
        this->bytes = 0;
        this->indentlevel = 0;

        this->buffs = nullptr;
        std::memset(this->data, 0, sizeof(this->data));

        this->isIOEmit = isIOEmit;
    }
        
    void BSQEmitBufferMgr::writeSlow(char c)
    {
        if(this->cpos == this->epos) {
            BSQIOBuffer newbuf = xxxx; //CALL ALLOCATOR HERE TO GET A NEW BUFFER -- either from IO or from GC Runtime -- depends on the output target
            this->buffers.push_back(newbuf);

            this->cpos = newbuf;
            this->epos = newbuf + BSQ_BUFFER_ALLOCATOR_BLOCK_SIZE;
        }

        *(this->cpos) = (uint8_t)c;
        this->cpos++;
        this->bytes++;
    }

    void BSQEmitBufferMgr::writeSlowTail(const char* str, size_t slen)
    {
        BSQIOBuffer newbuf = xxxx; //CALL ALLOCATOR HERE TO GET A NEW BUFFER -- either from IO or from GC Runtime -- depends on the output target
        this->buffers.push_back(newbuf);

        this->cpos = newbuf;
        this->epos = newbuf + BSQ_BUFFER_ALLOCATOR_BLOCK_SIZE;

        std::memcpy(this->cpos, str, slen);
        this->cpos += slen;
        this->bytes += slen;
    }
        
    ByteBufferBlock* BSQEmitBufferMgr::completeEmit(size_t& bytes)
    {
        this->cpos = nullptr;
        this->epos = nullptr;
        this->indentlevel = 0;

        bytes = this->bytes;
        this->bytes = 0;

        xxxx; //flush active buffer

        if(!this->isIOEmit) {
            xxxx; //release the GC root pin
        }

        return std::move(this->buffers);
    }

    void BSQONEmitter::emitNone()
    {
        this->bufferMgr.writeImmediate("none");
    }

    void BSQONEmitter::emitBool(Bool b)
    {
        if(Bool::toBool(b)) {
            this->bufferMgr.writeImmediate("true");
        }
        else {
            this->bufferMgr.writeImmediate("false");
        }
    }
        
    void BSQONEmitter::emitNat(Nat n)
    {
        this->bufferMgr.writeNumberWFormat("%llin", n.getValue());
    }

    void BSQONEmitter::emitInt(Int i)
    {
        this->bufferMgr.writeNumberWFormat("%llii", i.getValue());
    }

    void BSQONEmitter::emitChkNat(ChkNat n)
    {
        if(n.isBottom()) {
            this->bufferMgr.writeImmediate("#");
        }
        else {
            if(n.getValue() <= (__int128_t)std::numeric_limits<int64_t>::max()) {
                this->bufferMgr.writeNumberWFormat("%lliN", static_cast<int64_t>(n.getValue()));
            }
            else {
                assert(false); // Not Implemented: format for very large ChkNat values
            }
        }
    }

    void BSQONEmitter::emitChkInt(ChkInt i)
    {
        if(i.isBottom()) {
            this->bufferMgr.writeImmediate("#");
        }
        else {
            if(((__int128_t)std::numeric_limits<int64_t>::min() <= i.getValue()) & (i.getValue() <= (__int128_t)std::numeric_limits<int64_t>::max())) {
                this->bufferMgr.writeNumberWFormat("%lliI", static_cast<int64_t>(i.getValue()));
            }
            else {
                assert(false); // Not Implemented: format for very large ChkInt values
            }
        }
    }

    void BSQONEmitter::emitByte(Byte b)
    {
        this->bufferMgr.writeNumberWFormat("0x%x", b.getValue());
    }

    void BSQONEmitter::emitCChar(CChar c)
    {
        assert(false); // Not Implemented
    }

    void BSQONEmitter::emitUnicodeChar(UnicodeChar c)
    {
        assert(false); // Not Implemented
    }

    void BSQONEmitter::emitCString(CString s)
    {
        assert(false); // Not Implemented
    }

    void BSQONEmitter::emitString(String s)
    {
        assert(false); // Not Implemented
    }
}
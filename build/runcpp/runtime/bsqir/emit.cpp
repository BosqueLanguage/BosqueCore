#include "emit.h"

namespace ᐸRuntimeᐳ
{
    void BSQEmitBufferMgr::prepForEmit(bool isIOEmit)
    {
        this->cdata = g_alloc_info.io_buffer_alloc();

        this->cpos = this->cdata;
        this->epos = this->cdata + MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE;
        this->bytes = 0;
        this->indentlevel = 0;

        std::memset(this->cdata, 0, MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE);
        this->iobuffs.clear();
    }
        
    void BSQEmitBufferMgr::rotateData()
    {
        this->iobuffs.push_back(this->cdata);
        this->cdata = g_alloc_info.io_buffer_alloc();

        this->cpos = this->cdata;
        this->epos = this->cdata + MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE;
        
        std::memset(this->cdata, 0, MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE);
    }

    void BSQEmitBufferMgr::writeSlow(char c)
    {
        if(this->cpos == this->epos) {
            this->rotateData();
        }

        *(this->cpos) = (uint8_t)c;
        this->cpos++;
        this->bytes++;
    }

    void BSQEmitBufferMgr::writeSlowTail(const char* str, size_t slen)
    {
        this->rotateData();

        std::memcpy(this->cpos, str, slen);
        this->cpos += slen;
        this->bytes += slen;
    }
        
    std::list<uint8_t*>&& BSQEmitBufferMgr::completeEmit(size_t& bytes)
    {
        this->rotateData();
        bytes = this->bytes;
        
        this->indentlevel = 0;
        this->bytes = 0;

        return std::move(this->iobuffs);
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
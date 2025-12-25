#include "emit.h"

namespace ᐸRuntimeᐳ
{
    void BSQEmitBufferMgr::prepForEmit()
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
        this->iobuffs.push_back(this->cdata);
        bytes = this->bytes;
     
        this->cdata = nullptr;
        this->cpos = nullptr;
        this->epos = nullptr;
        this->indentlevel = 0;
        this->bytes = 0;

        return std::move(this->iobuffs);
    }

    void BSQONEmitter::emitNone(XNone n)
    {
        this->bufferMgr.writeImmediate("none");
    }

    void BSQONEmitter::emitBool(XBool b)
    {
        if(XBool::toBool(b)) {
            this->bufferMgr.writeImmediate("true");
        }
        else {
            this->bufferMgr.writeImmediate("false");
        }
    }
        
    void BSQONEmitter::emitNat(XNat n)
    {
        this->bufferMgr.writeNumberWFormat("%llin", n.value);
    }

    void BSQONEmitter::emitInt(XInt i)
    {
        this->bufferMgr.writeNumberWFormat("%llii", i.value);
    }

    void BSQONEmitter::emitChkNat(XChkNat n)
    {
        if(n.isBottom()) {
            this->bufferMgr.writeImmediate("ChkNat::npos");
        }
        else {
            if(n.value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
                this->bufferMgr.writeNumberWFormat("%lliN", static_cast<int64_t>(n.value));
            }
            else {
                assert(false); // Not Implemented: format for very large ChkNat values
            }
        }
    }

    void BSQONEmitter::emitChkInt(XChkInt i)
    {
        if(i.isBottom()) {
            this->bufferMgr.writeImmediate("ChkInt::npos");
        }
        else {
            if(((__int128_t)std::numeric_limits<int64_t>::min() <= i.value) & (i.value <= (__int128_t)std::numeric_limits<int64_t>::max())) {
                this->bufferMgr.writeNumberWFormat("%lliI", static_cast<int64_t>(i.value));
            }
            else {
                assert(false); // Not Implemented: format for very large ChkInt values
            }
        }
    }

    void BSQONEmitter::emitFloat(XFloat f)
    {
        if(std::floor(f.value) != f.value) {
            this->bufferMgr.writeNumberWFormat("%lgf", f.value);
        }
        else {
            //force the decimal and a single trailing 0 for whole numbers
            this->bufferMgr.writeNumberWFormat("%lg.0f", f.value);
        }
    }

    void BSQONEmitter::emitByte(XByte b)
    {
        this->bufferMgr.writeNumberWFormat("0x%x", b.value);
    }

    void BSQONEmitter::emitCChar(XCChar c)
    {
        assert(false); // Not Implemented
    }

    void BSQONEmitter::emitUnicodeChar(XUnicodeChar c)
    {
        assert(false); // Not Implemented
    }

    void BSQONEmitter::emitCString(XCString s)
    {
        assert(false); // Not Implemented
    }

    void BSQONEmitter::emitString(XString s)
    {
        assert(false); // Not Implemented
    }

    std::list<uint8_t*>&& BSQONEmitter::completeEmit(size_t& bytes)
    {
        return this->bufferMgr.completeEmit(bytes);
    }
}

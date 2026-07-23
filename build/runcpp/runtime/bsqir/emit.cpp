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
        if((bool)b) {
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
            this->bufferMgr.writeNumberWFormat("%.12lgf", f.value);
        }
        else {
            //force the decimal and a single trailing 0 for whole numbers
            this->bufferMgr.writeNumberWFormat("%.12lg.0f", f.value);
        }
    }

    void BSQONEmitter::emitByte(XByte b)
    {
        this->bufferMgr.writeNumberWFormat("0x%x", b.value);
    }

    void BSQONEmitter::emitCChar(XCChar c)
    {
        this->bufferMgr.writeImmediate("c'");

        if(!isMustEscapeCChar((char)c.value)) {
            this->bufferMgr.write((char)c.value);            
        }
        else {
            auto ii = std::find_if(s_escape_names_char_simple.begin(), s_escape_names_char_simple.end(), [c](const std::pair<uint8_t, const char*>& p) { return p.first == (uint8_t)c.value; });
            if(ii != s_escape_names_char_simple.end()) {
                this->bufferMgr.write(ii->second);
            }
            else {
                this->bufferMgr.writeNumberWFormat("%%x%x;", c.value);
            }
        }

        this->bufferMgr.writeImmediate("'");
    }

    void BSQONEmitter::emitUnicodeChar(XUnicodeChar c)
    {
        this->bufferMgr.writeImmediate("c\"");
        
        if(!isMustEscapeUnicodeChar((char32_t)c.value)) {
            this->bufferMgr.write((char)c.value);
        }
        else {
            auto ii = std::find_if(s_escape_names_unicode_simple.begin(), s_escape_names_unicode_simple.end(), [c](const std::pair<uint8_t, const char*>& p) { return p.first == (char32_t)c.value; });
            if(ii != s_escape_names_unicode_simple.end()) {
                this->bufferMgr.write(ii->second);
            }
            else {
                //TODO: maybe we want to do some selective multi-byte emits here for nicer output, but for now just emit the hex value as it is the least problematic encoding
                
                this->bufferMgr.writeNumberWFormat("%%x%x;", c.value);
            }
        }
        
        this->bufferMgr.writeImmediate("\"");
    }

    void BSQONEmitter::emitCString(XCString s)
    {
        this->bufferMgr.writeImmediate("'");

        XCStringIterator istart = s.begin();
        XCStringIterator iend = s.end();

        for(auto ii = istart; ii != iend; ++ii) {
            char c = *ii;

            if(!isMustEscapeCChar(c)) {
                this->bufferMgr.write(c);
            }
            else {
                auto escname = std::find_if(s_escape_names_char_simple.begin(), s_escape_names_char_simple.end(), [c](const std::pair<uint8_t, const char*>& p) { return p.first == c; });
                if(escname != s_escape_names_char_simple.end()) {
                    this->bufferMgr.write(escname->second);
                }
                else {
                    this->bufferMgr.writeNumberWFormat("%%x%x;", c);
                }
            }
        }

        this->bufferMgr.writeImmediate("'");
    }

    void BSQONEmitter::emitString(XString s)
    {
        this->bufferMgr.writeImmediate("\"");

        XStringIterator istart = s.begin();
        XStringIterator iend = s.end();

        for(auto ii = istart; ii != iend; ++ii) {
            char32_t c = *ii;

            if(!isMustEscapeUnicodeChar(c)) {
                this->bufferMgr.write((char)c);
            }
            else {
                auto ii = std::find_if(s_escape_names_unicode_simple.begin(), s_escape_names_unicode_simple.end(), [c](const std::pair<uint8_t, const char*>& p) { return p.first == (char32_t)c; });
                if(ii != s_escape_names_unicode_simple.end()) {
                    this->bufferMgr.write(ii->second);
                }
                else {
                    //TODO: maybe we want to do some selective multi-byte emits here for nicer output, but for now just emit the hex value as it is the least problematic encoding

                    this->bufferMgr.writeNumberWFormat("%%x%x;", c);
                }
            }
        }

        this->bufferMgr.writeImmediate("\"");
    }

    void BSQONEmitter::emitCRegex(XCRegex r)
    {
        assert(false); // Not Implemented: emitting CRegex values
    }
    
    void emitRegex(XRegex r)
    {
        assert(false); // Not Implemented: emitting Regex values
    }

    std::list<uint8_t*>&& BSQONEmitter::completeEmit(size_t& bytes)
    {
        return this->bufferMgr.completeEmit(bytes);
    }

    void BSQONEmitter::debug_emit(const std::function<void()>& emitter)
    {
        size_t obytes = 0;
        this->prepForEmit(true);
        emitter();
        auto oibb = this->completeEmit(obytes);

        //TODO assume chars are all printable for now
        for(size_t i = 0; i < obytes; i++) {
            printf("%c", static_cast<char>(oibb.front()[i]));
        }
        printf("\n");

        ᐸRuntimeᐳ::g_alloc_info.io_buffer_free_list(oibb);
        oibb.clear();
    }

    void DiagnosticsEmitter::emitNone(std::ostream& out, XNone n)
    {
        out << "none";
    }
    
    void DiagnosticsEmitter::emitBool(std::ostream& out, XBool b)
    {
        out << (bool)b;
    }

    void DiagnosticsEmitter::emitNat(std::ostream& out, XNat n)
    {
        out << n.value << "n";
    }

    void DiagnosticsEmitter::emitInt(std::ostream& out, XInt i)
    {
        out << i.value << "i";
    }

    void DiagnosticsEmitter::emitChkNat(std::ostream& out, XChkNat n)
    {
        if(n.isBottom()) {
            out << "ChkNat::npos";
        }
        else {
            if(n.value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
                out << (int64_t)n.value << "N";
            }
            else {
                assert(false); // Not Implemented: format for very large ChkNat values
            }
        }
    }

    void DiagnosticsEmitter::emitChkInt(std::ostream& out, XChkInt i)
    {
        if(i.isBottom()) {
            out << "ChkInt::npos";
        }
        else {
            if(i.value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
                out << (int64_t)i.value << "I";
            }
            else {
                assert(false); // Not Implemented: format for very large ChkNat values
            }
        }
    }

    void DiagnosticsEmitter::emitFloat(std::ostream& out, XFloat f)
    {
        if(std::floor(f.value) != f.value) {
            out << f.value << "f";
        }
        else {
            out << f.value << ".0f";
        }
    }

    void DiagnosticsEmitter::emitByte(std::ostream& out, XByte b)
    {
        assert(false); // Not Implemented: emitting Byte values
    }

    void DiagnosticsEmitter::emitCChar(std::ostream& out, XCChar c)
    {
        //TODO: we need to handle escaping correctly
        out << "c'" << char(c.value) << "'";
    }

    void DiagnosticsEmitter::emitUnicodeChar(std::ostream& out, XUnicodeChar c)
    {
        //TODO: we need to handle escaping correctly
        out << "c\"" << char(c.value) << "\"";
    }

    void DiagnosticsEmitter::emitCString(std::ostream& out, XCString s)
    {
        s.diagnosticEmit(out, true);
    }
        
    void DiagnosticsEmitter::emitString(std::ostream& out, XString s)
    {
        s.diagnosticEmit(out, true);
    }

    void DiagnosticsEmitter::emitCRegex(std::ostream& out, XCRegex r)
    {
        assert(false); // Not Implemented: emitting CRegex values
    }

    void DiagnosticsEmitter::emitRegex(std::ostream& out, XRegex r)
    {
        assert(false); // Not Implemented: emitting Regex values
    }
}

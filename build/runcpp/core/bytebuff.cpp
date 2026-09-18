#include "bytebuff.h"

namespace ᐸRuntimeᐳ
{
    thread_local GCAllocator<ByteBufferEntry> ByteBufferEntry_allocator(&g_typeinfo_ByteBufferEntry);
    thread_local GCAllocator<ByteBufferBlock> ByteBufferBlock_allocator(&g_typeinfo_ByteBufferBlock);

    const TypeInfo* XByteBuffer::s_entrytypeinfo = &g_typeinfo_ByteBufferEntry;
    thread_local GCAllocator<ByteBufferEntry>* XByteBuffer::s_entryallocator = &ByteBufferEntry_allocator;
    const TypeInfo* XByteBuffer::s_blocktypeinfo = &g_typeinfo_ByteBufferBlock;
    thread_local GCAllocator<ByteBufferBlock>* XByteBuffer::s_blockallocator = &ByteBufferBlock_allocator;

    void jsonParseToBSQ_ByteBuffer(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array(), "JSON -> BSQ", 0, nullptr, "Expected JSON array for ByteBuffer");

        size_t jlen = j.size();
        ByteBufferStreamingBuilder builder{};
        for(size_t i = 0; i < jlen; ++i)
        {
            const json& elem = j[i];
            bsq_validate(elem.is_number_unsigned(), "JSON -> BSQ", 0, nullptr, "Expected JSON number for ByteBuffer element");
            bsq_validate(elem.get<uint64_t>() <= std::numeric_limits<uint8_t>::max(), "JSON -> BSQ", 0, nullptr, "Byte overflow in ByteBuffer element");

            builder.appendByte(static_cast<uint8_t>(elem.get<uint64_t>()));
        }

        *((XByteBuffer*)resptr) = builder.finalize();
    }

    void parseToBSQ_ByteBuffer(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralByteBuffer, "BAPI -> BSQ", 0, nullptr, "Expected LiteralByteBuffer token");
     
        size_t tlen = lexer->getCurrentTokenDataSize();
        if(tlen == 4) {
            *((XByteBuffer*)resptr) = XByteBuffer{};
        }
        else {
            //eat 0x and (the [ gets handled in the loop)
            size_t cpos = 2; 
            IOBufferIterator ii = lexer->getCurrentTokenIterator();
            ++ii;
            ++ii;

            ByteBufferStreamingBuilder builder{};
            while(cpos < tlen - 1) { //ignore the closing ']' of the LiteralByteBuffer
                uint8_t bb = *ii;
                bsq_validate(bb == ',' || bb == '[', "BAPI -> BSQ", 0, nullptr, "Expected ',' separator or '[' start in LiteralByteBuffer");
                ++cpos;
                ++ii;
                    
                while(std::isspace(*ii)) {
                    ++cpos;
                    ++ii;
                }

                //read hex value
                char outbuff[16] = {0};
                size_t ecount = 0;
                while(std::isxdigit(*ii) && ecount < 4) {
                    outbuff[ecount] = *ii;
                    ++ecount;
                    ++cpos;
                    ++ii;
                }

                uint8_t output = 0;
                auto [ptr, ec] = std::from_chars(outbuff, outbuff + ecount, output, 16);

                bsq_validate(ec == std::errc() && (ptr == outbuff + ecount), "BAPI -> BSQ", 0, nullptr, "Failed to parse hex value for LiteralByteBuffer element");
                builder.appendByte(output);

                while(std::isspace(*ii)) {
                    ++cpos;
                    ++ii;
                }
            }

            *((XByteBuffer*)resptr) = builder.finalize();
        }

        lexer->consume();
    }

    json bsqToJSON_ByteBuffer(const TypeInfo* tinfo, const void* valptr)
    {
        const XByteBuffer* buffer = (const XByteBuffer*)valptr;
        
        json result = json::array();
        if(buffer->isInline()) {
            const uint8_t* inlinedata = buffer->inlinedata();
            for(size_t i = 0; i < buffer->bytes(); ++i) {
                result.push_back(inlinedata[i]);
            }
        }
        else {
            for(auto ii = buffer->begin(); ii != buffer->end(); ++ii) {
                result.push_back(*ii);
            }
        }

        return result;
    }

    void bsqToBAPI_ByteBuffer(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const XByteBuffer* buffer = (const XByteBuffer*)valptr;
        std::array<char, 64> numbuf;

        builder->appendConstString("0x[");
        if(buffer->isInline()) {
            const uint8_t* inlinedata = buffer->inlinedata();
            for(size_t i = 0; i < buffer->bytes(); ++i) {
                if(i != 0) {
                    builder->appendConstString(",");
                }

                size_t written = std::snprintf(numbuf.data(), numbuf.size(), "%x", inlinedata[i]);
                builder->appendConstString(numbuf.data(), written);
            }
        }
        else {
            bool first = true;
            for(auto ii = buffer->begin(); ii != buffer->end(); ++ii) {
                if(!first) {
                    builder->appendConstString(",");
                }
                first = false;

                size_t written = std::snprintf(numbuf.data(), numbuf.size(), "%x", *ii);
                builder->appendConstString(numbuf.data(), written);
            }
        }
        builder->appendChar(']');
    }

    void displayValue_ByteBuffer(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const XByteBuffer* buffer = (const XByteBuffer*)valptr;
        std::array<char, 64> numbuf;

        os << getDisplayIndent(indent) << "0x[";
        if(buffer->isInline()) {
            const uint8_t* inlinedata = buffer->inlinedata();
            for(size_t i = 0; i < buffer->bytes(); ++i) {
                if(i != 0) {
                    os << ",";
                }

                size_t written = std::snprintf(numbuf.data(), numbuf.size(), "%x", inlinedata[i]);
                os << numbuf.data();
            }
        }
        else {
            bool first = true;
            for(auto ii = buffer->begin(); ii != buffer->end(); ++ii) {
                if(!first) {
                    os << ",";
                }
                first = false;

                size_t written = std::snprintf(numbuf.data(), numbuf.size(), "%x", *ii);
                os << numbuf.data();
            }
        }
        os << "]";
    }
}

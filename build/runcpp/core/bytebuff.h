#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

namespace ᐸRuntimeᐳ 
{
    class ByteBufferEntry
    {
    public:
        constexpr static size_t BUFFER_ENTRY_SIZE = 64;

        std::array<uint8_t, BUFFER_ENTRY_SIZE> data;

        ByteBufferEntry() : data{} { ; }
        ByteBufferEntry(const std::array<uint8_t, BUFFER_ENTRY_SIZE>& data) : data{data} { ; }
        ByteBufferEntry(const ByteBufferEntry& other) = default;

        ByteBufferEntry(const std::initializer_list<uint8_t>& initdata) : data{} { std::copy(initdata.begin(), initdata.end(), this->data.begin()); }

        uint8_t* getData() { return this->data.data(); }
        const uint8_t* getData() const { return this->data.data(); }

        uint8_t getInner(size_t index) const { return this->data[index]; }
    };

    class ByteBufferBlock
    {
    public:
        constexpr static size_t BUFFER_BLOCK_ENTRY_COUNT = 63; //TODO: This may need tuning, seems like a reasonable default for now (time vs wasted space tradeoff) -- this struct is 64 fields

        std::array<ByteBufferEntry*, BUFFER_BLOCK_ENTRY_COUNT> entries;
        ByteBufferBlock* next;

        ByteBufferBlock() : entries{}, next{} { ; }
        ByteBufferBlock(const std::array<ByteBufferEntry*, BUFFER_BLOCK_ENTRY_COUNT>& entries, ByteBufferBlock* next) : entries{entries}, next{next} { ; } 
        ByteBufferBlock(const ByteBufferBlock& other) = default;
    };

    inline constexpr TypeInfo g_typeinfo_ByteBufferEntry = {
        WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY,
        sizeof(ByteBufferEntry),
        byteSizeToSlotCount(sizeof(ByteBufferEntry)),
        LayoutTag::Ref,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "ByteBufferEntry",
        true
    };

    inline constexpr TypeInfo g_typeinfo_ByteBufferBlock = {
        WELL_KNOWN_TYPE_ID_BYTEBUFFERBLOCK,
        sizeof(ByteBufferBlock),
        byteSizeToSlotCount(sizeof(ByteBufferBlock)),
        LayoutTag::Ref,
        "111111111111111111111111111111111111111111111111111111111111111",
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "ByteBufferBlock",
        false
    };

    inline constexpr TypeInfo g_typeinfo_ByteBuffer = {
        WELL_KNOWN_TYPE_ID_BYTEBUFFER,
        32,
        byteSizeToSlotCount(32),
        LayoutTag::Value,
        "0001",
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "ByteBuffer",
        false
    };

    class ByteBufferIterator
    {
    private:
        ByteBufferEntry* centry;
        size_t cindex;
        
        ByteBufferBlock* cblock;
        size_t bbindex;

        size_t gindex;
        size_t totalbytes;

    public:
        ByteBufferIterator(ByteBufferEntry* e, ByteBufferBlock* b, size_t totalbytes) : centry{e}, cindex{0}, cblock{b}, bbindex{0}, gindex{0}, totalbytes{totalbytes} { ; }
        ByteBufferIterator(const ByteBufferIterator& other) = default;

        inline bool valid() const 
        {
            return (this->gindex < totalbytes);
        }

        inline uint8_t get() const 
        {
            return this->centry->data[this->cindex];
        }

        inline size_t getIndex() const 
        {
            return this->gindex;
        }

        void nextslow()
        {
            if(this->gindex < this->totalbytes) {
                this->bbindex++;

                if(this->bbindex >= ByteBufferBlock::BUFFER_BLOCK_ENTRY_COUNT) {
                    this->cblock = this->cblock->next;
                    this->bbindex = 0;
                }
                
                this->centry = this->cblock->entries[this->bbindex];
                this->cindex = 0;
            }
        }

        inline void next() 
        {
            this->gindex++;

            if(this->cindex + 1 < ByteBufferEntry::BUFFER_ENTRY_SIZE) {
                this->cindex++;
            }
            else {
                this->nextslow();
            }
        }
    };

    class XByteBuffer
    {
    public:
        constexpr static size_t BUFFER_INLINE_SIZE = 16;

    private:
        size_t bytesize;
        std::array<uint8_t, BUFFER_INLINE_SIZE> inlinebytes;
        void* heapbytes;

    public:
        XByteBuffer() : bytesize{0}, inlinebytes{}, heapbytes{} { ; }
        XByteBuffer(const std::array<uint8_t, BUFFER_INLINE_SIZE>& i, size_t b) :  bytesize{b}, inlinebytes{i}, heapbytes{} { ; }
        XByteBuffer(void* h, size_t b) :  bytesize{b}, inlinebytes{}, heapbytes{h} { ; }
        XByteBuffer(const XByteBuffer& other) = default;

        size_t bytes() const { return this->bytesize; }

        ByteBufferIterator iterator() const 
        {
            //should special case for small buffers
            assert(this->bytesize > BUFFER_INLINE_SIZE);

            if(this->bytesize <= ByteBufferEntry::BUFFER_ENTRY_SIZE) {
                return ByteBufferIterator(static_cast<ByteBufferEntry*>(this->heapbytes), nullptr, this->bytesize);
            }
            else {
                ByteBufferBlock* root = static_cast<ByteBufferBlock*>(this->heapbytes);
                return ByteBufferIterator(root->entries[0], root, this->bytesize);
            }
        }
    };
}

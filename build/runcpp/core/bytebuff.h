#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

namespace ᐸRuntimeᐳ 
{
    class ByteBufferEntry
    {
    public:
        constexpr static size_t BUFFER_ENTRY_SIZE = 512; //TODO: This may need tuning, seems like a reasonable default for now (time vs wasted space tradeoff)

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

    union ByteBufferTreeUnion
    {
        void* upunning;
        ByteBufferEntry* buff;
        ByteBufferBlock* node;

        ByteBufferTreeUnion() : upunning{} { ; }
        ByteBufferTreeUnion(ByteBufferEntry* b) : buff{b} { ; }
        ByteBufferTreeUnion(ByteBufferBlock* n) : node{n} { ; }
        ByteBufferTreeUnion(const ByteBufferTreeUnion& other) = default;

        ByteBufferTreeUnion& operator=(const ByteBufferTreeUnion& other)
        {
            if(this == &other) {
                return *this;
            }

            this->upunning = other.upunning;
            return *this;
        }
    };
    using BufferTree = ᐸRuntimeᐳ::BoxedUnion<ByteBufferTreeUnion>;

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
        sizeof(BufferTree) + sizeof(size_t),
        byteSizeToSlotCount(sizeof(BufferTree) + sizeof(size_t)),
        LayoutTag::Value,
        "200",
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
    private:
        BufferTree tree;
        size_t bytesize;

    public:
        XByteBuffer() : tree{}, bytesize{0} { ; }
        XByteBuffer(const BufferTree& t, size_t b) : tree{t}, bytesize{b} { ; }
        XByteBuffer(const XByteBuffer& other) = default;

        XByteBuffer(ByteBufferEntry* b, size_t size) : tree{ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ByteBufferTreeUnion>{&ᐸRuntimeᐳ::g_typeinfo_ByteBufferEntry, ᐸRuntimeᐳ::ByteBufferTreeUnion(b)}}, bytesize{size} { ; }
        XByteBuffer(ByteBufferBlock* n, size_t size) : tree{ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ByteBufferTreeUnion>{&ᐸRuntimeᐳ::g_typeinfo_ByteBufferBlock, ᐸRuntimeᐳ::ByteBufferTreeUnion(n)}}, bytesize{size} { ; }

        size_t bytes() const { return this->bytesize; }

        ByteBufferIterator iterator() const 
        {
            if(this->tree.typeinfo->bsqtypeid == ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY) {
                return ByteBufferIterator(this->tree.data.buff, nullptr, this->bytesize);
            }
            else {
                ByteBufferBlock* root = this->tree.data.node;
                return ByteBufferIterator(root->entries[0], root, this->bytesize);
            }
        }
    };
}

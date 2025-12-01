#pragma once

#include "../common.h"
#include "../boxed.h"

namespace ᐸRuntimeᐳ 
{
    class ByteBufferEntry
    {
    public:
        constexpr static size_t BUFFER_ENTRY_SIZE = 512; //TODO: This may need tuning, seems like a reasonable default for now (time vs wasted space tradeoff)

        uint8_t data[BUFFER_ENTRY_SIZE];

        constexpr ByteBufferEntry() : data{0} {}
        constexpr ByteBufferEntry(const std::initializer_list<uint8_t>& initdata) : data{0} { std::copy(initdata.begin(), initdata.end(), this->data); }
        constexpr ByteBufferEntry(const ByteBufferEntry& other) = default;

        inline constexpr uint8_t* getData() { return this->data; }
        inline constexpr const uint8_t* getData() const { return this->data; }

        inline constexpr uint8_t getInner(size_t index) const { return this->data[index]; }
        inline constexpr uint8_t getFull(size_t index, uint8_t value) const { return this->data[index % BUFFER_ENTRY_SIZE]; }
    };

    class ByteBufferBlock
    {
    public:
        constexpr static size_t BUFFER_BLOCK_ENTRY_COUNT = 63; //TODO: This may need tuning, seems like a reasonable default for now (time vs wasted space tradeoff) -- this struct is 64 fields

        ByteBufferEntry* entries[BUFFER_BLOCK_ENTRY_COUNT];
        ByteBufferBlock* next;

        ByteBufferBlock(size_t entryCount) : entries{0}, next(nullptr) {}
        ByteBufferBlock(ByteBufferEntry** entries, size_t entryCount, ByteBufferBlock* next) : entries{0}, next(next) { std::copy(entries, entries + entryCount, this->entries); }
        ByteBufferBlock(const ByteBufferBlock& other) = default;

        inline constexpr ByteBufferEntry* getEntryFor(size_t index) const 
        {
            constexpr size_t bbvolume = ByteBufferBlock::BUFFER_BLOCK_ENTRY_COUNT * ByteBufferEntry::BUFFER_ENTRY_SIZE;

            const ByteBufferBlock* curr = this;
            while(index >= bbvolume) {
                index -= bbvolume;
                curr = curr->next;
            }

            return this->entries[index / ByteBufferEntry::BUFFER_ENTRY_SIZE]; 
        }
    };

    union ByteBufferTreeUnion
    {
        ByteBufferEntry* buff;
        ByteBufferBlock* node;

        constexpr ByteBufferTreeUnion() : buff() {}
        constexpr ByteBufferTreeUnion(const ByteBufferTreeUnion& other) = default;
        constexpr ByteBufferTreeUnion(ByteBufferEntry* b) : buff(b) {}
        constexpr ByteBufferTreeUnion(ByteBufferBlock* n) : node(n) {}
    };
    using BufferTree = ᐸRuntimeᐳ::BoxedUnion<ByteBufferTreeUnion>;

    constexpr TypeInfoBase g_typeinfo_ByteBufferEntry = {
        WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY,
        sizeof(ByteBufferEntry),
        byteSizeToSlotCount(sizeof(ByteBufferEntry)),
        LayoutTag::Ref,
        BSQ_PTR_MASK_LEAF,
        "ByteBufferEntry",
        nullptr
    };

    constexpr TypeInfoBase g_typeinfo_ByteBufferBlock = {
        WELL_KNOWN_TYPE_ID_BYTEBUFFERBLOCK,
        sizeof(ByteBufferBlock),
        byteSizeToSlotCount(sizeof(ByteBufferBlock)),
        LayoutTag::Ref,
        "1111111111111111111111111111111111111111111111111111111111111111",
        "ByteBufferBlock",
        nullptr
    };

    constexpr TypeInfoBase g_typeinfo_ByteBuffer = {
        WELL_KNOWN_TYPE_ID_BYTEBUFFER,
        sizeof(BufferTree) + sizeof(size_t),
        byteSizeToSlotCount(sizeof(BufferTree) + sizeof(size_t)),
        LayoutTag::Tagged,
        "200",
        "ByteBuffer",
        nullptr
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
        ByteBufferIterator(ByteBufferEntry* e, ByteBufferBlock* b, size_t totalbytes) : centry(e), cindex(0), cblock(b), bbindex(0), gindex(0), totalbytes(totalbytes) {}
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

        //for lexing 
        inline void advance(size_t& startidx, size_t& endidx, size_t count)
        {
            startidx = this->gindex;
            endidx = startidx + count;
            for(size_t i = 0; i < count; i++) {
                this->next();
            }
        }

        inline void advanceWithExtract(size_t& startidx, size_t& endidx, char* outbuf, size_t count)
        {
            startidx = this->gindex;
            endidx = startidx + count;
            for(size_t i = 0; i < count; i++) {
                outbuf[i] = (char)this->get();
                this->next();
            }
            outbuf[count] = '\0';
        }
    };

    class ByteBuffer
    {
    private:
        BufferTree tree;
        size_t bytesize;

    public:
        constexpr ByteBuffer() : tree(), bytesize(0) {}
        constexpr ByteBuffer(ByteBufferEntry* b) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ByteBufferTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_ByteBufferEntry, ᐸRuntimeᐳ::ByteBufferTreeUnion(b))), bytesize(ByteBufferEntry::BUFFER_ENTRY_SIZE) {}
        ByteBuffer(ByteBufferBlock* n) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ByteBufferTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_ByteBufferBlock, ᐸRuntimeᐳ::ByteBufferTreeUnion(n))), bytesize(0) {}
        ByteBuffer(const BufferTree& t, size_t b) : tree(t), bytesize(b) {}
        ByteBuffer(const ByteBuffer& other) = default;

        inline constexpr size_t bytes() const { return this->bytesize; }

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

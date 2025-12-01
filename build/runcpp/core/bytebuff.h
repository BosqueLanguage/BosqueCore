#pragma once

#include "../../common.h"
#include "boxed.h"

namespace ᐸRuntimeᐳ 
{
    class ByteBufferEntry
    {
    public:
        constexpr static size_t BUFFER_ENTRY_SIZE = 512; //TODO: This may need tuning, seems like a reasonable default for now (time vs wasted space tradeoff)

        uint8_t data[BUFFER_ENTRY_SIZE];

        constexpr ByteBufferEntry() noexcept : data{0} {}
        constexpr ByteBufferEntry(const std::initializer_list<uint8_t>& initdata) noexcept : data{0} { std::copy(initdata.begin(), initdata.end(), this->data); }
        constexpr ByteBufferEntry(const ByteBufferEntry& other) noexcept = default;

        inline constexpr uint8_t* getData() noexcept { return this->data; }
        inline constexpr const uint8_t* getData() const noexcept { return this->data; }

        inline constexpr uint8_t getInner(size_t index) const noexcept { return this->data[index]; }
        inline constexpr uint8_t getFull(size_t index, uint8_t value) const noexcept { return this->data[index % BUFFER_ENTRY_SIZE]; }
    };

    class ByteBufferBlock
    {
    public:
        constexpr static size_t BUFFER_BLOCK_ENTRY_COUNT = 63; //TODO: This may need tuning, seems like a reasonable default for now (time vs wasted space tradeoff) -- this struct is 64 fields

        ByteBufferEntry* entries[BUFFER_BLOCK_ENTRY_COUNT];
        ByteBufferBlock* next;

        ByteBufferBlock(size_t entryCount) noexcept : entries{0}, next(nullptr) {}
        ByteBufferBlock(ByteBufferEntry* entries, size_t entryCount, ByteBufferBlock* next) noexcept : entries{0}, next(next) { std::copy(entries, entries + entryCount, this->entries); }
        ByteBufferBlock(const ByteBufferBlock& other) noexcept = default;

        inline constexpr ByteBufferEntry* getEntryFor(size_t index) const noexcept 
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

    union ᐸByteBufferTreeUnionᐳ
    {
        ByteBufferEntry* buff;
        ByteBufferBlock* node;

        constexpr ᐸByteBufferTreeUnionᐳ() noexcept : buff() {}
        constexpr ᐸByteBufferTreeUnionᐳ(const ᐸByteBufferTreeUnionᐳ& other) noexcept = default;
        constexpr ᐸByteBufferTreeUnionᐳ(ByteBufferEntry* b) noexcept : buff(b) {}
        constexpr ᐸByteBufferTreeUnionᐳ(ByteBufferBlock* n) noexcept : node(n) {}
    };
    using BufferTree = ᐸRuntimeᐳ::BoxedUnion<ᐸByteBufferTreeUnionᐳ>;

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
        ByteBufferIterator(ByteBufferEntry* e, ByteBufferBlock* b, size_t totalbytes) noexcept : centry(e), cindex(0), cblock(b), bbindex(0), gindex(0), totalbytes(totalbytes) {}
        ByteBufferIterator(const ByteBufferIterator& other) noexcept = default;

        inline bool valid() const noexcept 
        {
            return (this->gindex < totalbytes);
        }

        inline uint8_t get() const noexcept 
        {
            return this->centry->data[this->cindex];
        }

        void nextslow() noexcept
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

        inline void next() noexcept 
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

    class ByteBuffer
    {
    private:
        BufferTree tree;
        size_t bytes;

    public:
        constexpr ByteBuffer() noexcept : tree(), bytes(0) {}
        constexpr ByteBuffer(ByteBufferEntry* b) noexcept : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ᐸByteBufferTreeUnionᐳ>(&ᐸRuntimeᐳ::g_typeinfo_ByteBufferEntry, ᐸRuntimeᐳ::ᐸByteBufferTreeUnionᐳ(b))), bytes(ByteBufferEntry::BUFFER_ENTRY_SIZE) {}
        ByteBuffer(ByteBufferBlock* n) noexcept : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ᐸByteBufferTreeUnionᐳ>(&ᐸRuntimeᐳ::g_typeinfo_ByteBufferBlock, ᐸRuntimeᐳ::ᐸByteBufferTreeUnionᐳ(n))), bytes(0) {}
        ByteBuffer(const BufferTree& t, size_t b) noexcept : tree(t), bytes(b) {}
        ByteBuffer(const ByteBuffer& other) noexcept = default;

        inline constexpr size_t bytes() const noexcept { return this->bytes; }

        ByteBufferIterator iterator() const noexcept 
        {
            if(this->tree.typeinfo->bsqtypeid == ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY) {
                return ByteBufferIterator(this->tree.data.buff, nullptr, this->bytes);
            }
            else {
                ByteBufferBlock* root = this->tree.data.node;
                return ByteBufferIterator(root->entries[0], root, this->bytes);
            }
        }
    };
}

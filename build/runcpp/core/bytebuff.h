#pragma once

#include "../common.h"

#include "bsqtype.h"

#include "../runtime/allocator/alloc.h"

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

        template<typename Iter>
        ByteBufferEntry(Iter begin, Iter end) : data{} { std::copy(begin, end, this->data.begin()); }

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
    public:
        ByteBufferEntry* centry;
        size_t cindex;
        
        ByteBufferBlock* cblock;
        size_t bbindex;

        size_t gindex;
        size_t totalbytes;

    private:
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

    public:
        using value_type = uint8_t;
        using iterator_category = std::forward_iterator_tag;
        using difference_type = std::ptrdiff_t;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            return this->centry->data[this->cindex];
        }

        ByteBufferIterator& operator++()
        {
            this->gindex++;
            
            if(this->cindex + 1 < ByteBufferEntry::BUFFER_ENTRY_SIZE) {
                this->cindex++;
            }
            else {
                this->nextslow();
            }

            return *this;
        }
 
        ByteBufferIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }
 
        friend bool operator==(const ByteBufferIterator& lhs, const ByteBufferIterator& rhs)
        {
            return lhs.gindex == rhs.gindex;
        }

        friend bool operator!=(const ByteBufferIterator& lhs, const ByteBufferIterator& rhs) 
        {
            return lhs.gindex != rhs.gindex;
        }
    };
    static_assert(std::forward_iterator<ByteBufferIterator>);

    class XByteBuffer
    {
    public:
        constexpr static size_t BUFFER_INLINE_SIZE = 16;

        static const TypeInfo* s_entrytypeinfo;
        thread_local static GCAllocator<ByteBufferEntry>* s_entryallocator;

        static const TypeInfo* s_blocktypeinfo;
        thread_local static GCAllocator<ByteBufferBlock>* s_blockallocator;

    private:
        size_t bytesize;
        std::array<uint8_t, BUFFER_INLINE_SIZE> inlinebytes;
        void* heapbytes;

    public:
        constexpr XByteBuffer() : bytesize{0}, inlinebytes{}, heapbytes{} { ; }
        constexpr XByteBuffer(const std::array<uint8_t, BUFFER_INLINE_SIZE>& i, size_t b) :  bytesize{b}, inlinebytes{i}, heapbytes{} { ; }
        XByteBuffer(void* h, size_t b) :  bytesize{b}, inlinebytes{}, heapbytes{h} { ; }
        XByteBuffer(const XByteBuffer& other) = default;

        template<typename Iter>
        static XByteBuffer mk(Iter begin, Iter end, size_t size)
        {
            if(size == 0) {
                return XByteBuffer{};
            }
            else {
                if(size <= BUFFER_INLINE_SIZE) {
                    std::array<uint8_t, BUFFER_INLINE_SIZE> inlinebytes{};
                    std::copy(begin, end, inlinebytes.begin());

                    return XByteBuffer(inlinebytes, size);
                }
                else {
                    if(size <= ByteBufferEntry::BUFFER_ENTRY_SIZE) {
                        return XByteBuffer(XByteBuffer::s_entryallocator->allocate(begin, end), size);
                    }
                    else {
                        ByteBufferBlock* blockl = nullptr;
                        size_t bytecount = 0;
                        std::array<uint8_t, ByteBufferEntry::BUFFER_ENTRY_SIZE> entrybytes{};
                        size_t blockcount = 0;
                        std::array<ByteBufferEntry*, ByteBufferBlock::BUFFER_BLOCK_ENTRY_COUNT> entryptrs{};

                        auto iter = begin;
                        while(iter != end) {
                            while(bytecount < ByteBufferEntry::BUFFER_ENTRY_SIZE && iter != end) {
                                entrybytes[bytecount] = *iter;

                                bytecount++;
                                ++iter;
                            }

                            ByteBufferEntry* bb = XByteBuffer::s_entryallocator->allocate(entrybytes);
                            entrybytes.fill(0);
                            bytecount = 0;

                            entryptrs[blockcount] = bb;
                            blockcount++;
                            if(blockcount == ByteBufferBlock::BUFFER_BLOCK_ENTRY_COUNT) {
                                blockl = XByteBuffer::s_blockallocator->allocate(entryptrs, blockl);
                                entryptrs.fill(nullptr);
                                blockcount = 0;
                            }
                        }
                        if(blockcount != 0) {
                            blockl = XByteBuffer::s_blockallocator->allocate(entryptrs, blockl);
                        }

                        //reverse for flow
                        ByteBufferBlock* revl = nullptr;
                        while(blockl != nullptr) {
                            revl = XByteBuffer::s_blockallocator->allocate(blockl->entries, revl);
                            blockl = blockl->next;
                        }

                        return XByteBuffer(revl, size);
                    }
                }
            }
        }

        static XByteBuffer mk(const std::initializer_list<uint8_t>& elems)
        {
            return XByteBuffer::mk(elems.begin(), elems.end(), elems.size());
        }

        constexpr size_t bytes() const { return this->bytesize; }

        constexpr bool isInline() const { return this->bytesize <= BUFFER_INLINE_SIZE; }

        const uint8_t* inlinedata() const { return this->inlinebytes.data(); }

        ByteBufferIterator begin() const 
        {
            //should special case for small buffers
            assert(this->bytesize > BUFFER_INLINE_SIZE);

            if(this->bytesize <= ByteBufferEntry::BUFFER_ENTRY_SIZE) {
                return ByteBufferIterator{static_cast<ByteBufferEntry*>(this->heapbytes), 0, nullptr, 0, 0, this->bytesize};
            }
            else {
                ByteBufferBlock* root = static_cast<ByteBufferBlock*>(this->heapbytes);
                return ByteBufferIterator{root->entries[0], 0, root, 0, 0, this->bytesize};
            }
        }

        ByteBufferIterator end() const 
        {
            //should special case for small buffers
            assert(this->bytesize > BUFFER_INLINE_SIZE);

            return ByteBufferIterator{nullptr, 0, nullptr, 0, this->bytesize, this->bytesize};
        }
    };
}

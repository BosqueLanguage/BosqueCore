#include "bytebuff.h"


namespace ᐸRuntimeᐳ
{
    thread_local GCAllocator<ByteBufferEntry> ByteBufferEntry_allocator(&g_typeinfo_ByteBufferEntry);
    thread_local GCAllocator<ByteBufferBlock> ByteBufferBlock_allocator(&g_typeinfo_ByteBufferBlock);

    const TypeInfo* XByteBuffer::s_entrytypeinfo = &g_typeinfo_ByteBufferEntry;
    thread_local GCAllocator<ByteBufferEntry>* XByteBuffer::s_entryallocator = &ByteBufferEntry_allocator;
    const TypeInfo* XByteBuffer::s_blocktypeinfo = &g_typeinfo_ByteBufferBlock;
    thread_local GCAllocator<ByteBufferBlock>* XByteBuffer::s_blockallocator = &ByteBufferBlock_allocator;

    XByteBuffer XByteBuffer::mk(const std::initializer_list<uint8_t>& elems)
    {
        if(elems.size() == 0) {
            return XByteBuffer{};
        }
        else {
            if(elems.size() <= BUFFER_INLINE_SIZE) {
                std::array<uint8_t, BUFFER_INLINE_SIZE> inlinebytes{};
                std::copy(elems.begin(), elems.end(), inlinebytes.begin());

                return XByteBuffer(inlinebytes, elems.size());
            }
            else {
                if(elems.size() <= ByteBufferEntry::BUFFER_ENTRY_SIZE) {
                    return XByteBuffer(XByteBuffer::s_entryallocator->allocate(elems), elems.size());
                }
                else {
                    ByteBufferBlock* blockl = nullptr;
                    size_t bytecount = 0;
                    std::array<uint8_t, ByteBufferEntry::BUFFER_ENTRY_SIZE> entrybytes{};
                    size_t blockcount = 0;
                    std::array<ByteBufferEntry*, ByteBufferBlock::BUFFER_BLOCK_ENTRY_COUNT> entryptrs{};

                    auto iter = elems.begin();
                    while(iter != elems.end()) {
                        while(bytecount < ByteBufferEntry::BUFFER_ENTRY_SIZE && iter != elems.end()) {
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

                    //reverse for flow
                    std::stack<ByteBufferBlock*> blockstack{};
                    while(blockl != nullptr) {
                        blockstack.push(blockl);
                        blockl = blockl->next;
                    }

                    ByteBufferBlock* revl = nullptr;
                    while(!blockstack.empty()) {
                        ByteBufferBlock* bb = blockstack.top();
                        blockstack.pop();
                        revl = XByteBuffer::s_blockallocator->allocate(bb->entries, revl);
                    }

                    return XByteBuffer(revl, elems.size());
                }
            }
        }
    }
}

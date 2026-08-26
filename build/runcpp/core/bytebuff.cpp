#include "bytebuff.h"


namespace ᐸRuntimeᐳ
{
    thread_local GCAllocator<ByteBufferEntry> ByteBufferEntry_allocator(&g_typeinfo_ByteBufferEntry);
    thread_local GCAllocator<ByteBufferBlock> ByteBufferBlock_allocator(&g_typeinfo_ByteBufferBlock);

    const TypeInfo* XByteBuffer::s_entrytypeinfo = &g_typeinfo_ByteBufferEntry;
    thread_local GCAllocator<ByteBufferEntry>* XByteBuffer::s_entryallocator = &ByteBufferEntry_allocator;
    const TypeInfo* XByteBuffer::s_blocktypeinfo = &g_typeinfo_ByteBufferBlock;
    thread_local GCAllocator<ByteBufferBlock>* XByteBuffer::s_blockallocator = &ByteBufferBlock_allocator;
}

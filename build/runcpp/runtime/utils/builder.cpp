#include "builder.h"

#include "../allocator/alloc.h"

namespace ᐸRuntimeᐳ
{
    std::string getDisplayIndent(std::optional<std::string> indent)
    {
        return indent.has_value() ? indent.value() : "";
    }

    void IOBufferStreamingBuilder::rotateData()
    {
        uint8_t* nbuff = g_alloc_info.io_buffer_alloc();
        std::memset(nbuff, 0, MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE);

        this->cpos = nbuff;
        this->epos = nbuff + MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE;
        this->iobuffs.push_back(nbuff);
    }

    void IOBufferStreamingBuilder::writeSlow(uint8_t c)
    {
        if(this->cpos == this->epos) {
            this->rotateData();
        }

        *(this->cpos) = (uint8_t)c;
        this->cpos++;
        this->totalbytes++;
    }

    void IOBufferStreamingBuilder::writeSlowTail(const char* str, size_t slen)
    {
        assert(slen < MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE); //I don't think this can (should) ever happen but assert for sanity

        this->rotateData();

        std::memcpy(this->cpos, str, slen);
        this->cpos += slen;
        this->totalbytes += slen;
    }
}

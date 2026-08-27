#include "common.h"
#include "runtime/taskinfo.h"

namespace ᐸRuntimeᐳ
{
    thread_local BosqueThreadLocalInfo tl_bosque_info;

    void bsq_handle_error(const char* file, uint32_t line, ErrorKind kerror, const char* tag, const char* message)
    {
        ᐸRuntimeᐳ::tl_bosque_info.current_task->pending_error = { file, line, kerror, tag, message }; 
        std::longjmp(ᐸRuntimeᐳ::tl_bosque_info.current_task->error_handler, 11);
    }

    size_t multibyteCharCount(uint8_t c) 
    {
        if((c & 0x80) == 0) {
            return 1;
        }
        else if((c & 0xE0) == 0xC0) {
            return 2;
        }
        else if((c & 0xF0) == 0xE0) {
            return 3;
        }
        else if((c & 0xF8) == 0xF0) {
            return 4;
        }
        return 0;
    }

    size_t ucharToMultiByteEncoding(char32_t c, std::array<uint8_t, 4>& outbuff)
    {
        assert(c > 0x7F);
        
        if(c <= 0x7FF) {
            outbuff = { (uint8_t)(0xC0 | (c >> 6)), (uint8_t)(0x80 | (c & 0x3F)), 0, 0 };
            return 2;
        }
        else if(c <= 0xFFFF) {
            outbuff = { (uint8_t)(0xE0 | (c >> 12)), (uint8_t)(0x80 | ((c >> 6) & 0x3F)), (uint8_t)(0x80 | (c & 0x3F)), 0 };
            return 3;
        }
        else {
            outbuff = { (uint8_t)(0xF0 | (c >> 18)), (uint8_t)(0x80 | ((c >> 12) & 0x3F)), (uint8_t)(0x80 | ((c >> 6) & 0x3F)), (uint8_t)(0x80 | (c & 0x3F)) };
            return 4;
       }
    }

    char32_t multibyteToUChar(const std::array<uint8_t, 4>& inbuff, size_t bytecount)
    {
        assert(bytecount != 1);

        //TODO: we need to review this invalid encoding setup 
        //      Specifically we are not handling overlong UTF-8 encodings or invalid byte sequences rigorously.

        if(bytecount == 2) {
            return (char32_t)((inbuff[0] & 0x1F) << 6 | (inbuff[1] & 0x3F));
        }
        else if(bytecount == 3) {
            return (char32_t)((inbuff[0] & 0x0F) << 12 | ((inbuff[1] & 0x3F) << 6) | (inbuff[2] & 0x3F));
        }
        else {
            return (char32_t)((inbuff[0] & 0x07) << 18 | ((inbuff[1] & 0x3F) << 12) | ((inbuff[2] & 0x3F) << 6) | (inbuff[3] & 0x3F));
        }
    }
}

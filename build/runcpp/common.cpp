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

        // 2-byte (0xC2 - 0xDF) -- 0xC0 and 0xC1 are strictly overlong
        if(inbuff[0] >= 0xC2 && inbuff[0] <= 0xDF) {
            if ((inbuff[1] & 0xC0) != 0x80) {
                return std::numeric_limits<char32_t>::max();
            }
        }

        // 3-byte sequence (0xE0 - 0xEF)
        if (inbuff[0] >= 0xE0 && inbuff[0] <= 0xEF) {
            if((inbuff[1] & 0xC0) != 0x80 || (inbuff[2] & 0xC0) != 0x80) {
                return std::numeric_limits<char32_t>::max();
            }

            // Overlong check: If b1 == 0xE0, b2 must be >= 0xA0
            if(inbuff[0] == 0xE0 && inbuff[1] < 0xA0) {
                return std::numeric_limits<char32_t>::max();
            }
            
            // Surrogate pair rejection (0xED 0xA0 0x80 to 0xED 0xBF 0xBF)
            if (inbuff[0] == 0xED && inbuff[1] >= 0xA0) {
                return std::numeric_limits<char32_t>::max();
            }
        }

        // 4-byte sequence (0xF0 - 0xF4)
        if(inbuff[0] >= 0xF0 && inbuff[0] <= 0xF4) {
            uint8_t b2 = static_cast<uint8_t>(inbuff[1]);
            uint8_t b3 = static_cast<uint8_t>(inbuff[2]);
            uint8_t b4 = static_cast<uint8_t>(inbuff[3]);

            if ((inbuff[1] & 0xC0) != 0x80 || (inbuff[2] & 0xC0) != 0x80 || (inbuff[3] & 0xC0) != 0x80) {
                return std::numeric_limits<char32_t>::max();
            }

            // Overlong check: If inbuff[0] == 0xF0, b2 must be >= 0x90
            if (inbuff[0] == 0xF0 && inbuff[1] < 0x90) {
                return std::numeric_limits<char32_t>::max();
            }
            
            // Code point limit check: UTF-8 bounds end at 0xF4 0x8F 0xBF 0xBF (U+10FFFF)
            if (inbuff[0] == 0xF4 && inbuff[1] > 0x8F) {
                return std::numeric_limits<char32_t>::max();
            }

        }

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

#include "encodings.h"

namespace ᐸRuntimeᐳ
{
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

    size_t ucharToMultiByteEncoding(char32_t c, std::array<uint8_t, 64>& outbuff)
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

    /* Given a buffer that contains and encoded CChar (either named or numeric) get the char value (or return false if invalid) */
    bool processEncodedCChar(const std::array<uint8_t, 64>& inbuff, size_t bytecount, char& outchar)
    {
        uint8_t c = inbuff[0];
        
        if(c != '%') { 
            if(bytecount != 1) {
                return false;
            }

            outchar = c;
            return isLegalCChar(c) && !isMustEscapeCChar(c);
        }
        else {
            if(bytecount < 2 || inbuff[bytecount - 1] != ';') {
                return false;
            }

            const char* iichars = reinterpret_cast<const char*>(inbuff.data());
            auto ii = std::find_if(s_escape_names_char.cbegin(), s_escape_names_char.cend(), [&](const auto& p) { 
                return p.second.first == bytecount && std::equal(iichars, iichars + bytecount, p.second.second, p.second.second + p.second.first); 
            });

            if(ii != s_escape_names_char.cend()) {
                outchar = static_cast<char>(ii->first);
                return true;
            }
            else {
                if(inbuff[1] != 'x') {
                    return false;
                }

                uint8_t output = 0;
                auto [ptr, ec] = std::from_chars(iichars + 2, iichars + bytecount - 1, output, 16);

                outchar = static_cast<char>(output);
                return ec == std::errc() && (ptr == iichars + bytecount - 1) && isLegalCChar(output);
            }
        }
    }

    bool processEncodedUnicodeChar(const std::array<uint8_t, 64>& inbuff, size_t bytecount, char32_t& outchar)
    {
        char32_t c = inbuff[0];
        
        if(c != U'%') { 
            if(bytecount != 1) {
                return false;
            }

            outchar = c;
            return isLegalUnicodeChar(c) && !isMustEscapeUnicodeChar(c);
        }
        else {
            if(bytecount < 2 || inbuff[bytecount - 1] != ';') {
                return false;
            }

            const char* iichars = reinterpret_cast<const char*>(inbuff.data());
            auto ii = std::find_if(s_escape_names_unicode.cbegin(), s_escape_names_unicode.cend(), [&](const auto& p) { 
                return p.second.first == bytecount && std::equal(iichars, iichars + bytecount, p.second.second, p.second.second + p.second.first); 
            });

            if(ii != s_escape_names_unicode.cend()) {
                outchar = static_cast<char32_t>(ii->first);
                return true;
            }
            else {
                if(inbuff[1] != 'x') {
                    return false;
                }

                uint32_t output = 0;
                auto [ptr, ec] = std::from_chars(iichars + 2, iichars + bytecount - 1, output, 16);

                outchar = static_cast<char32_t>(output);
                return ec == std::errc() && (ptr == iichars + bytecount - 1) && isLegalUnicodeChar(output);
            }
        }
    }
}

#pragma once

#include "../../common.h"

namespace ᐸRuntimeᐳ 
{
    constexpr std::array<std::pair<char32_t, std::pair<size_t, const char*>>, 68> s_escape_names_unicode = {
        std::make_pair<char32_t, std::pair<size_t, const char*>>(0, {strlen("%NUL;"), "%NUL;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(1, {strlen("%SOH;"), "%SOH;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(2, {strlen("%STX;"), "%STX;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(3, {strlen("%ETX;"), "%ETX;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(4, {strlen("%EOT;"), "%EOT;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(5, {strlen("%ENQ;"), "%ENQ;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(6, {strlen("%ACK;"), "%ACK;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(7, {strlen("%a;"), "%a;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(8, {strlen("%b;"), "%b;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(9, {strlen("%t;"), "%t;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(10, {strlen("%n;"), "%n;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(11, {strlen("%v;"), "%v;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(12, {strlen("%f;"), "%f;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(13, {strlen("%r;"), "%r;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(14, {strlen("%SO;"), "%SO;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(15, {strlen("%SI;"), "%SI;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(16, {strlen("%DLE;"), "%DLE;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(17, {strlen("%DC1;"), "%DC1;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(18, {strlen("%DC2;"), "%DC2;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(19, {strlen("%DC3;"), "%DC3;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(20, {strlen("%DC4;"), "%DC4;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(21, {strlen("%NAK;"), "%NAK;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(22, {strlen("%SYN;"), "%SYN;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(23, {strlen("%ETB;"), "%ETB;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(24, {strlen("%CAN;"), "%CAN;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(25, {strlen("%EM;"), "%EM;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(26, {strlen("%SUB;"), "%SUB;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(27, {strlen("%e;"), "%e;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(28, {strlen("%FS;"), "%FS;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(29, {strlen("%GS;"), "%GS;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(30, {strlen("%RS;"), "%RS;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(31, {strlen("%US;"), "%US;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(127, {strlen("%DEL;"), "%DEL;"}),

        std::make_pair<char32_t, std::pair<size_t, const char*>>(32, {strlen("%space;"), "%space;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(33, {strlen("%bang;"), "%bang;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(34, {strlen("%;"), "%;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(34, {strlen("%quote;"), "%quote;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(35, {strlen("%hash;"), "%hash;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(36, {strlen("%dollar;"), "%dollar;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(37, {strlen("%%;"), "%%;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(37, {strlen("%percent;"), "%percent;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(38, {strlen("%amp;"), "%amp;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(39, {strlen("%tick;"), "%tick;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(40, {strlen("%lparen;"), "%lparen;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(41, {strlen("%rparen;"), "%rparen;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(42, {strlen("%star;"), "%star;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(43, {strlen("%plus;"), "%plus;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(44, {strlen("%comma;"), "%comma;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(45, {strlen("%dash;"), "%dash;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(46, {strlen("%dot;"), "%dot;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(47, {strlen("%slash;"), "%slash;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(58, {strlen("%colon;"), "%colon;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(59, {strlen("%semicolon;"), "%semicolon;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(60, {strlen("%langle;"), "%langle;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(61, {strlen("%equal;"), "%equal;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(62, {strlen("%rangle;"), "%rangle;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(63, {strlen("%question;"), "%question;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(64, {strlen("%at;"), "%at;"}), 
        std::make_pair<char32_t, std::pair<size_t, const char*>>(91, {strlen("%lbracket;"), "%lbracket;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(92, {strlen("%backslash;"), "%backslash;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(93, {strlen("%rbracket;"), "%rbracket;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(94, {strlen("%caret;"), "%caret;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(95, {strlen("%underscore;"), "%underscore;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(96, {strlen("%backtick;"), "%backtick;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(123, {strlen("%lbrace;"), "%lbrace;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(124, {strlen("%pipe;"), "%pipe;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(125, {strlen("%rbrace;"), "%rbrace;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(126, {strlen("%tilde;"), "%tilde;"})
    };

    constexpr std::array<std::pair<char32_t, std::pair<size_t, const char*>>, 4> s_escape_names_unicode_simple = {
        std::make_pair<char32_t, std::pair<size_t, const char*>>(9, {strlen("%t;"), "%t;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(10, {strlen("%n;"), "%n;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(34, {strlen("%;"), "%;"}),
        std::make_pair<char32_t, std::pair<size_t, const char*>>(37, {strlen("%%;"), "%%;"})
    };

    constexpr std::array<std::pair<uint8_t, std::pair<size_t, const char*>>, 37> s_escape_names_char = {
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(9, {std::strlen("%t;"), "%t;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(10, {std::strlen("%n;"), "%n;"}),

        std::make_pair<uint8_t, std::pair<size_t, const char*>>(32, {std::strlen("%space;"), "%space;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(33, {std::strlen("%bang;"), "%bang;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(34, {std::strlen("%quote;"), "%quote;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(35, {std::strlen("%hash;"), "%hash;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(36, {std::strlen("%dollar;"), "%dollar;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(37, {std::strlen("%%;"), "%%;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(37, {std::strlen("%percent;"), "%percent;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(38, {std::strlen("%amp;"), "%amp;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(39, {std::strlen("%;"), "%;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(39, {std::strlen("%tick;"), "%tick;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(40, {std::strlen("%lparen;"), "%lparen;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(41, {std::strlen("%rparen;"), "%rparen;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(42, {std::strlen("%star;"), "%star;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(43, {std::strlen("%plus;"), "%plus;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(44, {std::strlen("%comma;"), "%comma;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(45, {std::strlen("%dash;"), "%dash;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(46, {std::strlen("%dot;"), "%dot;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(47, {std::strlen("%slash;"), "%slash;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(58, {std::strlen("%colon;"), "%colon;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(59, {std::strlen("%semi;"), "%semi;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(60, {std::strlen("%langle;"), "%langle;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(61, {std::strlen("%equal;"), "%equal;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(62, {std::strlen("%rangle;"), "%rangle;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(63, {std::strlen("%question;"), "%question;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(64, {std::strlen("%at;"), "%at;"}), 
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(91, {std::strlen("%lbracket;"), "%lbracket;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(92, {std::strlen("%backslash;"), "%backslash;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(93, {std::strlen("%rbracket;"), "%rbracket;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(94, {std::strlen("%caret;"), "%caret;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(95, {std::strlen("%underscore;"), "%underscore;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(96, {std::strlen("%backtick;"), "%backtick;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(123, {std::strlen("%lbrace;"), "%lbrace;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(124, {std::strlen("%pipe;"), "%pipe;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(125, {std::strlen("%rbrace;"), "%rbrace;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(126, {std::strlen("%tilde;"), "%tilde;"})
    };

    constexpr std::array<std::pair<uint8_t, std::pair<size_t, const char*>>, 4> s_escape_names_char_simple = {
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(9, {std::strlen("%t;"), "%t;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(10, {std::strlen("%n;"), "%n;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(37, {std::strlen("%%;"), "%%;"}),
        std::make_pair<uint8_t, std::pair<size_t, const char*>>(39, {std::strlen("%;"), "%;"})
    };

    inline bool isMustEscapeCChar(char c)
    {
        return (c == '%' || c == '\'' || c == '\t' || c == '\n');
    }

    inline bool isLegalCChar(uint8_t c)
    {
        return c <= 126 && (std::isprint(c) || (c == '\t') || (c == '\n'));
    }

    inline bool isLegalUnicodeChar(char32_t c)
    {
        //TODO: this might need some attention -- like minimal encodings etc.

        return (c <= 0x10FFFF) && !((0xD800 <= c) && (c <= 0xDFFF));
    }

    inline bool isMustEscapeUnicodeChar(char32_t c)
    {
        //TODO: we might need to handle other unicode newline or other breaking chars

        return (c < 32 || c == 127 || c == U'%' || c == U'"' || c == U'\t' || c == U'\n');
    }

    inline bool isTrimableWhitespace(char32_t c) {
        //TODO: we don't really handle unicode whitespace -- need to investigate the expected behavior and update this function accordingly
        
        return std::isspace(c);
    }

    inline bool isMultibyteEncoding(uint8_t c)
    {
        return (c & 0x80) != 0;
    }

    size_t multibyteCharCount(uint8_t c);
    char32_t multibyteToUChar(const std::array<uint8_t, 4>& inbuff, size_t bytecount);

    inline bool isSingleByteEncoding(char32_t c)
    {
        return c <= 0x7F;
    }

    size_t ucharToMultiByteEncoding(char32_t c, std::array<uint8_t, 64>& outbuff);

    /* Given a buffer that contains and encoded CChar (either named or numeric) get the char value (or return false if invalid) */
    bool processEncodedCChar(const std::array<uint8_t, 64>& inbuff, size_t bytecount, char& outchar);

    /* Given a buffer that contains and encoded UnicodeChar (either named or numeric) get the char32_t value (or return false if invalid) */
    bool processEncodedUnicodeChar(const std::array<uint8_t, 64>& inbuff, size_t bytecount, char32_t& outchar);
}

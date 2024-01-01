#include "common.h"

namespace BSQON
{
    std::vector<std::pair<char32_t, UnicodeString>> s_escape_names_unicode = {
        {0, U"0;"},
        {1, U"SOH;"},
        {2, U"STX;"},
        {3, U"ETX;"},
        {4, U"EOT;"},
        {5, U"ENQ;"},
        {6, U"ACK;"},
        {7, U"a;"},
        {8, U"b;"},
        {9, U"t;"},
        {10, U"n;"},
        {11, U"v;"},
        {12, U"f;"},
        {13, U"r;"},
        {14, U"SO;"},
        {15, U"SI;"},
        {16, U"DLE;"},
        {17, U"DC1;"},
        {18, U"DC2;"},
        {19, U"DC3;"},
        {20, U"DC4;"},
        {21, U"NAK;"},
        {22, U"SYN;"},
        {23, U"ETB;"},
        {24, U"CAN;"},
        {25, U"EM;"},
        {26, U"SUB;"},
        {27, U"e;"},
        {28, U"FS;"},
        {29, U"GS;"},
        {30, U"RS;"},
        {31, U"US;"},
        {127, U"DEL;"},

        {32, U"space;"},
        {33, U"bang;"},
        {34, U";"},
        {34, U"quote;"},
        {35, U"hash;"},
        {36, U"dollar;"},
        {37, U"%;"},
        {37, U"percent;"},
        {38, U"amp;"},
        {39, U"tick;"},
        {40, U"lparen;"},
        {41, U"rparen;"},
        {42, U"star;"},
        {43, U"plus;"},
        {44, U"comma;"},
        {45, U"dash;"},
        {46, U"dot;"},
        {47, U"slash;"},
        {58, U"colon;"},
        {59, U"semicolon;"},
        {60, U"langle;"},
        {61, U"equal;"},
        {62, U"rangle;"},
        {63, U"question;"},
        {64, U"at;"}, 
        {91, U"lbracket;"},
        {92, U"backslash;"},
        {93, U"rbracket;"},
        {94, U"caret;"},
        {95, U"underscore;"},
        {96, U"backtick;"},
        {123, U"lbrace;"},
        {124, U"pipe;"},
        {125, U"rbrace;"},
        {126, U"tilde;"}
    };

    std::vector<std::pair<char, std::string>> s_escape_names_ascii = {
        {0, "0;"},
        {1, "SOH;"},
        {2, "STX;"},
        {3, "ETX;"},
        {4, "EOT;"},
        {5, "ENQ;"},
        {6, "ACK;"},
        {7, "a;"},
        {8, "b;"},
        {9, "t;"},
        {10, "n;"},
        {11, "v;"},
        {12, "f;"},
        {13, "r;"},
        {14, "SO;"},
        {15, "SI;"},
        {16, "DLE;"},
        {17, "DC1;"},
        {18, "DC2;"},
        {19, "DC3;"},
        {20, "DC4;"},
        {21, "NAK;"},
        {22, "SYN;"},
        {23, "ETB;"},
        {24, "CAN;"},
        {25, "EM;"},
        {26, "SUB;"},
        {27, "e;"},
        {28, "FS;"},
        {29, "GS;"},
        {30, "RS;"},
        {31, "US;"},
        {127, "DEL;"},

        {32, "space;"},
        {33, "bang;"},
        {34, "quote;"},
        {35, "hash;"},
        {36, "dollar;"},
        {37, "%;"},
        {37, "percent;"},
        {38, "amp;"},
        {39, ";"},
        {39, "tick;"},
        {40, "lparen;"},
        {41, "rparen;"},
        {42, "star;"},
        {43, "plus;"},
        {44, "comma;"},
        {45, "dash;"},
        {46, "dot;"},
        {47, "slash;"},
        {58, "colon;"},
        {59, "semi;"},
        {60, "langle;"},
        {61, "equal;"},
        {62, "rangle;"},
        {63, "question;"},
        {64, "at;"}, 
        {91, "lbracket;"},
        {92, "backslash;"},
        {93, "rbracket;"},
        {94, "caret;"},
        {95, "underscore;"},
        {96, "backtick;"},
        {123, "lbrace;"},
        {124, "pipe;"},
        {125, "rbrace;"},
        {126, "tilde;"}
    };

    std::optional<char32_t> decodeHexEscape(std::string escc)
    {
        //1-4 digits and a ;
        if(escc.size() == 1 || 7 < escc.size()) {
            return std::nullopt;
        }

        uint32_t cval;
        auto sct = sscanf(escc.c_str(), "%x;", &cval);
        if(sct != 1) {
            return std::nullopt;
        }
        else {
            return std::make_optional<char32_t>((char32_t)cval);
        }
    }

    UnicodeString resolveEscapeUnicodeFromCode(uint8_t c)
    {
        auto ii = std::find_if(s_escape_names_unicode.cbegin(), s_escape_names_unicode.cend(), [c](const std::pair<char32_t, UnicodeString>& p) { return p.first == c; });
        return U"%" + ii->second;
    }

    uint8_t resolveEscapeUnicodeFromName(const UnicodeString& name)
    {
        auto ii = std::find_if(s_escape_names_unicode.cbegin(), s_escape_names_unicode.cend(), [name](const std::pair<char32_t, UnicodeString>& p) { return p.second == name; });
        return ii->first;
    }

    std::string resolveEscapeASCIIFromCode(uint8_t c)
    {
        auto ii = std::find_if(s_escape_names_ascii.cbegin(), s_escape_names_ascii.cend(), [c](const std::pair<char, std::string>& p) { return p.first == c; });
        return "%" + ii->second;
    }

    uint8_t resolveEscapeASCIIFromName(const std::string& name)
    {
        auto ii = std::find_if(s_escape_names_ascii.cbegin(), s_escape_names_ascii.cend(), [name](const std::pair<char, std::string>& p) { return p.second == name; });
        return ii->first;
    }

    std::optional<UnicodeString> unescapeString(const uint8_t* bytes, size_t length)
    {
        //assume string has "..." so we need to remove them

        std::string acc;
        for(size_t i = 1; i < length - 1; ++i) {
            uint8_t c = bytes[i];

            if(c == '%') {
                auto sc = std::find(bytes + i, bytes + length, ';');
                if(sc == bytes + length) {
                    return std::nullopt;
                }

                auto escc = std::string(bytes + i + 1, sc + 1);

                if(std::isdigit(escc[0])) {
                    //it should be a hex number of 1-4 digits
                    auto esc = decodeHexEscape(escc);
                    if(!esc.has_value()) {
                        return std::nullopt;
                    }

                    acc = std::move(acc) + std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(esc.value());
                }
                else {
                    auto uniescc = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.from_bytes(escc);
                    auto esc = resolveEscapeUnicodeFromName(uniescc);
                    if(esc == 0) {
                        return std::nullopt;
                    }

                    acc = std::move(acc) + (char)esc;
                }

                i += escc.size();
            }
            else {
                acc = std::move(acc) + (char)c;
            }
        }

        return std::make_optional(std::move(std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.from_bytes(acc)));
    }

    std::vector<uint8_t> escapeString(const UnicodeString& sv)
    {
        UnicodeString acc = U"";
        for(auto ii = sv.cbegin(); ii != sv.cend(); ++ii) {
            char32_t c = *ii;

            if(c == U'%' || c == U'"' || c == U'\n' || c == U'\t' || c == U'\r') {
                acc = std::move(acc) + resolveEscapeUnicodeFromCode(c);
            }
            else {
                acc = std::move(acc) + c;
            }
        }
        acc = std::move(acc) + U"";

        std::string utf8 = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(acc);

        std::vector<uint8_t> res(utf8.size());
        std::transform(utf8.cbegin(), utf8.cend(), res.begin(), [](char c) { return (uint8_t)c; });

        return res;
    }

    std::optional<std::string> unescapeASCIIString(const uint8_t* bytes, size_t length)
    {
        //assume string has '...' (or `...`) so we need to remove them

        std::string acc;
        for(size_t i = 1; i < length - 1; ++i) {
            uint8_t c = bytes[i];

            if(!std::isprint(c) && !std::iswspace(c)) {
                return std::nullopt;
            }

            if(c == '%') {
                auto sc = std::find(bytes + i, bytes + length, ';');
                if(sc == bytes + length) {
                    return std::nullopt;
                }

                auto escc = std::string(bytes + i + 1, sc + 1);
                if(std::isdigit(escc[0])) {
                    //it should be a hex number of 1-4 digits
                    auto esc = decodeHexEscape(escc);
                    if(!esc.has_value() || esc.value() > 127) {
                        return std::nullopt;
                    }

                    acc = std::move(acc) + (char)esc.value();
                }
                else {
                    auto esc = resolveEscapeASCIIFromName(escc);
                    if(esc == 0) {
                        return std::nullopt;
                    }

                    acc = std::move(acc) + (char)esc;
                }

                i += escc.size();
            }
            else {
                acc = std::move(acc) + (char)c;
            }
        }

        return std::make_optional(std::move(acc));
    }

    std::vector<uint8_t> escapeASCIIString(const std::string& sv)
    {
        std::string acc;
        for(auto ii = sv.cbegin(); ii != sv.cend(); ++ii) {
            char c = *ii;

            if(c == '%' || c == '\'' || c == '\n' || c == '\t' || c == '\r') {
                acc = std::move(acc) + resolveEscapeASCIIFromCode(c);
            }
            else {
                acc = std::move(acc) + c;
            }
        }

        std::vector<uint8_t> res(acc.size());
        std::transform(acc.cbegin(), acc.cend(), res.begin(), [](char c) { return (uint8_t)c; });

        return res;
    }
}

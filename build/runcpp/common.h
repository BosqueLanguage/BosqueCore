#pragma once

#include <cmath>
#include <cstring>
#include <csetjmp>

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#include <optional>
#include <chrono>
#include <random>
#include <string>
#include <array>
#include <vector>
#include <set>
#include <unordered_set>
#include <map>
#include <list>
#include <algorithm>

#include <regex>

#include <type_traits>
#include <concepts>

#include <execution>
#include <mutex>
#include <thread>

#include <sys/mman.h> //mmap

//Only for diagnostics
#include <assert.h>
#include <iostream>

#include "./flags.h"

namespace ᐸRuntimeᐳ
{
    constexpr int64_t BSQ_NUMERIC_DYNAMIC_RANGE_BASE = 4611686018427387903ll;
    constexpr __int128_t BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED = ((__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE * (__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE);

    enum class ErrorKind
    {
        Generic,
        OutOfMemory,
        RuntimeAssertion,

        NumericBounds,
        NumericUnderflow,
        DivisionByZero,

        InvalidCast,
        ExhaustiveCheck,

        UserAbort,
        UserAssertion,
        UserInvariant,
        UserValidation,
        UserPrecondition,
        UserPostcondition
    };

    class ErrorInfo
    {
    public:
        const char* file;
        uint32_t line;

        ErrorKind kerror;
        const char* tag; //optional
        const char* message; //optional
    };

    template <typename U> 
    concept ConceptUnionRepr = std::is_union<U>::value;

    //slow path error handler
    [[noreturn]] void bsq_handle_error(const char* file, uint32_t line, ErrorKind kerror, const char* tag, const char* message);


    inline void bsq_typeassert(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::InvalidCast, tag, message);
        }
    }

    [[noreturn]] inline void bsq_exhaustive(const char* file, uint32_t line, const char* message)
    {
        bsq_handle_error(file, line, ErrorKind::ExhaustiveCheck, nullptr, message);
    }

    [[noreturn]] inline void bsq_abort(const char* file, uint32_t line, const char* tag, const char* message)
    {
        bsq_handle_error(file, line, ErrorKind::UserAbort, tag, message);
    }

    inline void bsq_assert(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserAssertion, tag, message);
        }
    }

    inline void bsq_validate(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserValidation, tag, message);
        }
    }

    inline void bsq_invariant(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserInvariant, tag, message);
        }
    }

    inline void bsq_requires(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserPrecondition, tag, message);
        }
    }

    inline void bsq_ensures(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserPostcondition, tag, message);
        }
    }

    //forward declaration of types that are stored in a thread local way
    class TaskInfo;

    class BosqueThreadLocalInfo
    {
    public:
        TaskInfo* current_task;

        BosqueThreadLocalInfo() : current_task(nullptr) {}

        // Cannot copy or move thread local info
        BosqueThreadLocalInfo(const BosqueThreadLocalInfo&) = delete;
        BosqueThreadLocalInfo &operator=(const BosqueThreadLocalInfo&) = delete;

        static void generate_uuid4(char out[16])
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }

        static void generate_uuid7(char out[16])
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }
    };


    extern thread_local BosqueThreadLocalInfo tl_bosque_info;

    //See also allocator/alloc.h for allocator specific thread local and global info -- no other globals should be hanging around!

    constexpr std::array<std::pair<char32_t, const char*>, 95> s_escape_names_unicode = {
        std::make_pair<char32_t, const char*>(0, "%NUL;"),
        std::make_pair<char32_t, const char*>(1, "%SOH;"),
        std::make_pair<char32_t, const char*>(2, "%STX;"),
        std::make_pair<char32_t, const char*>(3, "%ETX;"),
        std::make_pair<char32_t, const char*>(4, "%EOT;"),
        std::make_pair<char32_t, const char*>(5, "%ENQ;"),
        std::make_pair<char32_t, const char*>(6, "%ACK;"),
        std::make_pair<char32_t, const char*>(7, "%a;"),
        std::make_pair<char32_t, const char*>(8, "%b;"),
        std::make_pair<char32_t, const char*>(9, "%t;"),
        std::make_pair<char32_t, const char*>(10, "%n;"),
        std::make_pair<char32_t, const char*>(11, "%v;"),
        std::make_pair<char32_t, const char*>(12, "%f;"),
        std::make_pair<char32_t, const char*>(13, "%r;"),
        std::make_pair<char32_t, const char*>(14, "%SO;"),
        std::make_pair<char32_t, const char*>(15, "%SI;"),
        std::make_pair<char32_t, const char*>(16, "%DLE;"),
        std::make_pair<char32_t, const char*>(17, "%DC1;"),
        std::make_pair<char32_t, const char*>(18, "%DC2;"),
        std::make_pair<char32_t, const char*>(19, "%DC3;"),
        std::make_pair<char32_t, const char*>(20, "%DC4;"),
        std::make_pair<char32_t, const char*>(21, "%NAK;"),
        std::make_pair<char32_t, const char*>(22, "%SYN;"),
        std::make_pair<char32_t, const char*>(23, "%ETB;"),
        std::make_pair<char32_t, const char*>(24, "%CAN;"),
        std::make_pair<char32_t, const char*>(25, "%EM;"),
        std::make_pair<char32_t, const char*>(26, "%SUB;"),
        std::make_pair<char32_t, const char*>(27, "%e;"),
        std::make_pair<char32_t, const char*>(28, "%FS;"),
        std::make_pair<char32_t, const char*>(29, "%GS;"),
        std::make_pair<char32_t, const char*>(30, "%RS;"),
        std::make_pair<char32_t, const char*>(31, "%US;"),
        std::make_pair<char32_t, const char*>(127, "%DEL;"),

        std::make_pair<char32_t, const char*>(32, "%space;"),
        std::make_pair<char32_t, const char*>(33, "%bang;"),
        std::make_pair<char32_t, const char*>(34, "%;"),
        std::make_pair<char32_t, const char*>(34, "%quote;"),
        std::make_pair<char32_t, const char*>(35, "%hash;"),
        std::make_pair<char32_t, const char*>(36, "%dollar;"),
        std::make_pair<char32_t, const char*>(37, "%%;"),
        std::make_pair<char32_t, const char*>(37, "%percent;"),
        std::make_pair<char32_t, const char*>(38, "%amp;"),
        std::make_pair<char32_t, const char*>(39, "%tick;"),
        std::make_pair<char32_t, const char*>(40, "%lparen;"),
        std::make_pair<char32_t, const char*>(41, "%rparen;"),
        std::make_pair<char32_t, const char*>(42, "%star;"),
        std::make_pair<char32_t, const char*>(43, "%plus;"),
        std::make_pair<char32_t, const char*>(44, "%comma;"),
        std::make_pair<char32_t, const char*>(45, "%dash;"),
        std::make_pair<char32_t, const char*>(46, "%dot;"),
        std::make_pair<char32_t, const char*>(47, "%slash;"),
        std::make_pair<char32_t, const char*>(58, "%colon;"),
        std::make_pair<char32_t, const char*>(59, "%semicolon;"),
        std::make_pair<char32_t, const char*>(60, "%langle;"),
        std::make_pair<char32_t, const char*>(61, "%equal;"),
        std::make_pair<char32_t, const char*>(62, "%rangle;"),
        std::make_pair<char32_t, const char*>(63, "%question;"),
        std::make_pair<char32_t, const char*>(64, "%at;"), 
        std::make_pair<char32_t, const char*>(91, "%lbracket;"),
        std::make_pair<char32_t, const char*>(92, "%backslash;"),
        std::make_pair<char32_t, const char*>(93, "%rbracket;"),
        std::make_pair<char32_t, const char*>(94, "%caret;"),
        std::make_pair<char32_t, const char*>(95, "%underscore;"),
        std::make_pair<char32_t, const char*>(96, "%backtick;"),
        std::make_pair<char32_t, const char*>(123, "%lbrace;"),
        std::make_pair<char32_t, const char*>(124, "%pipe;"),
        std::make_pair<char32_t, const char*>(125, "%rbrace;"),
        std::make_pair<char32_t, const char*>(126, "%tilde;")
    };

    constexpr std::array<std::pair<char32_t, const char*>, 4> s_escape_names_unicode_simple = {
        std::make_pair<char32_t, const char*>(9, "%t;"),
        std::make_pair<char32_t, const char*>(10, "%n;"),
        std::make_pair<char32_t, const char*>(34, "%;"),
        std::make_pair<char32_t, const char*>(37, "%%;")
    };

    bool isSimpleEscapeUnicodeChar(char32_t c)
    {
        return (c == 9 || c == 10 || c == 34 || c == 37);
    }

    bool isMustEscapeUnicodeChar(char32_t c)
    {
        return !(32 <= c && c <= 126) || isSimpleEscapeUnicodeChar(c);
    }

    constexpr std::array<std::pair<uint8_t, const char*>, 55> s_escape_names_char = {
        std::make_pair<uint8_t, const char*>(9, "%t;"),
        std::make_pair<uint8_t, const char*>(10, "%n;"),

        std::make_pair<uint8_t, const char*>(32, "%space;"),
        std::make_pair<uint8_t, const char*>(33, "%bang;"),
        std::make_pair<uint8_t, const char*>(34, "%quote;"),
        std::make_pair<uint8_t, const char*>(35, "%hash;"),
        std::make_pair<uint8_t, const char*>(36, "%dollar;"),
        std::make_pair<uint8_t, const char*>(37, "%%;"),
        std::make_pair<uint8_t, const char*>(37, "%percent;"),
        std::make_pair<uint8_t, const char*>(38, "%amp;"),
        std::make_pair<uint8_t, const char*>(39, "%;"),
        std::make_pair<uint8_t, const char*>(39, "%tick;"),
        std::make_pair<uint8_t, const char*>(40, "%lparen;"),
        std::make_pair<uint8_t, const char*>(41, "%rparen;"),
        std::make_pair<uint8_t, const char*>(42, "%star;"),
        std::make_pair<uint8_t, const char*>(43, "%plus;"),
        std::make_pair<uint8_t, const char*>(44, "%comma;"),
        std::make_pair<uint8_t, const char*>(45, "%dash;"),
        std::make_pair<uint8_t, const char*>(46, "%dot;"),
        std::make_pair<uint8_t, const char*>(47, "%slash;"),
        std::make_pair<uint8_t, const char*>(58, "%colon;"),
        std::make_pair<uint8_t, const char*>(59, "%semi;"),
        std::make_pair<uint8_t, const char*>(60, "%langle;"),
        std::make_pair<uint8_t, const char*>(61, "%equal;"),
        std::make_pair<uint8_t, const char*>(62, "%rangle;"),
        std::make_pair<uint8_t, const char*>(63, "%question;"),
        std::make_pair<uint8_t, const char*>(64, "%at;"), 
        std::make_pair<uint8_t, const char*>(91, "%lbracket;"),
        std::make_pair<uint8_t, const char*>(92, "%backslash;"),
        std::make_pair<uint8_t, const char*>(93, "%rbracket;"),
        std::make_pair<uint8_t, const char*>(94, "%caret;"),
        std::make_pair<uint8_t, const char*>(95, "%underscore;"),
        std::make_pair<uint8_t, const char*>(96, "%backtick;"),
        std::make_pair<uint8_t, const char*>(123, "%lbrace;"),
        std::make_pair<uint8_t, const char*>(124, "%pipe;"),
        std::make_pair<uint8_t, const char*>(125, "%rbrace;"),
        std::make_pair<uint8_t, const char*>(126, "%tilde;")
    };

    constexpr std::array<std::pair<uint8_t, const char*>, 55> s_escape_names_char_simple = {
        std::make_pair<uint8_t, const char*>(9, "%t;"),
        std::make_pair<uint8_t, const char*>(10, "%n;"),
        std::make_pair<uint8_t, const char*>(37, "%%;"),
        std::make_pair<uint8_t, const char*>(39, "%;")
    };

    inline bool isSimpleEscapeCChar(char c)
    {
        return (c == 9 || c == 10 || c == 37 || c == 39);
    }

    inline bool isMustEscapeCChar(char c)
    {
        return !(40 <= c && c <= 126) || isSimpleEscapeCChar(c);
    }

    inline bool isLegalCChar(char c)
    {
        if(c > 126) {
            return false;
        }
        else {
            return std::isprint(c) || (c == '\t') || (c == '\n');
        }
    }

    inline bool isLegalUnicodeChar(char32_t c)
    {
        return (c <= 0x10FFFF) && !((0xD800 <= c) && (c <= 0xDFFF));
    }

    inline bool isMultibyteEncoding(char c)
    {
        return (c & 0x80) != 0;
    }
}

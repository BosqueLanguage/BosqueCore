#pragma once


#include "../../common.h"
#include "../../core/bytebuff.h" // For ByteBuffer iterator

namespace ᐸRuntimeᐳ
{
    enum class BSQONTokenType
    {
        Invalid = 0,
        ErrorToken,
        EOFToken,
        LiteralNone,
        LiteralTrue,
        LiteralFalse,
        LiteralNat,
        LiteralInt,
        LiteralChkNat,
        LiteralChkInt
    };

    class BSQONToken
    {
    public:
        BSQONTokenType tokentype;
        size_t startindex;
        size_t endindex;

        char scvalue[32]; // Simple constant value storage for small literals (bool, nat, int, uuidv4)

        BSQONToken() noexcept : tokentype(BSQONTokenType::Invalid), startindex(0), endindex(0), scvalue{0} {}
        BSQONToken(const BSQONToken& other) noexcept = default;
    };

    class BSQONLexer
    {
    private:
        //iterator may be defined over GC ByteBuffer or IO ByteBuffer (both represented via the same ByteBuffer and iterator structure for lexing)
        ByteBufferIterator iter;
        BSQONToken ctoken;

        static bool testchar(const ByteBufferIterator& ii, char c) noexcept;
        static bool testchars(ByteBufferIterator ii, const char* chars) noexcept;

        bool tryLexNone() noexcept;
        bool tryLexBool() noexcept;

        bool lexIntegralHelper(bool negok, char suffix) noexcept;
        bool tryLexNat() noexcept;
        bool tryLexInt() noexcept;
        bool tryLexChkNat() noexcept;
        bool tryLexChkInt() noexcept;

    public:
        BSQONLexer(const ByteBufferIterator& iter) noexcept : iter(iter), ctoken() {}

        const BSQONToken& current() const noexcept { return this->ctoken; }
        void consume() noexcept;
    };
}

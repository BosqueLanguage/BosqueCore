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

        BSQONToken() : tokentype(BSQONTokenType::Invalid), startindex(0), endindex(0), scvalue{0} {}
        BSQONToken(const BSQONToken& other) = default;
    };

    class BSQONLexer
    {
    private:
        //iterator may be defined over GC ByteBuffer or IO ByteBuffer (both represented via the same ByteBuffer and iterator structure for lexing)
        ByteBufferIterator iter;
        BSQONToken ctoken;

        static bool testchar(const ByteBufferIterator& ii, char c);
        static bool testchars(ByteBufferIterator ii, const char* chars);

        bool tryLexNone();
        bool tryLexBool();

        bool lexIntegralHelper(bool negok, char suffix);
        bool tryLexNat();
        bool tryLexInt();
        bool tryLexChkNat();
        bool tryLexChkInt();

    public:
        BSQONLexer(const ByteBufferIterator& iter) : iter(iter), ctoken() {}

        const BSQONToken& current() const { return this->ctoken; }
        void consume();
    };
}

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
        LiteralBool,
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
        ByteBufferIterator it;
        BSQONToken ctoken;

    public:
        BSQONLexer(const ByteBuffer& buff) noexcept : it(buff.iterator()), ctoken() {}

        const BSQONToken& current() const noexcept { return this->ctoken; }
        void consume() noexcept;
    };
}

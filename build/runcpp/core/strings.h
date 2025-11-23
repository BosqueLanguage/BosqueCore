#pragma once

#include "../common.h"
#include "boxed.h"

namespace Core 
{
    namespace ᐸRuntimeᐳ
    {
        enum class RColor : uint64_t
        {
            Red,
            Black
        };

        union CStrTree;

        class CStrBase
        {
        public:
            size_t length;

            constexpr CStrBase(size_t len) noexcept : length(len) {}
        };

        class CStrBuff : public CStrBase
        {
        public:
            constexpr static size_t CSTR_BUFF_SIZE = 24;

            char data[CSTR_BUFF_SIZE];

            constexpr CStrBuff() noexcept : CStrBase(0), data{0} {}

            template<size_t len>
            constexpr static CStrBuff literal(const char (&cstr)[len]) noexcept
            {
                static_assert(len - 1 <= ᐸRuntimeᐳ::CStrBuff::CSTR_BUFF_SIZE, "CString literal too large for CStrBuff");

                CStrBuff cb(len - 1);
                std::copy(cstr, cstr + len - 1, cb.data);

                return cb;
            }

            constexpr CStrBuff(const CStrBuff& other) noexcept = default;

            constexpr size_t size() const noexcept { return this->length; }
            constexpr char at(size_t index) const noexcept { return this->data[index]; }
        };

        class CStrNode : public CStrBase
        {
        public:
            RColor color;
            CStrTree* left;
            CStrTree* right;

            constexpr CStrNode() noexcept : CStrBase(0), color(RColor::Black), left(nullptr), right(nullptr) {}
            constexpr CStrNode(size_t len, RColor c, CStrTree* l, CStrTree* r) noexcept : CStrBase(len), color(c), left(l), right(r) {}
            
            constexpr CStrNode(const CStrNode& other) noexcept = default;
        };

        union ᐸCStrTreeUnionᐳ
        {
            CStrBuff buff;
            CStrNode node;

            constexpr ᐸCStrTreeUnionᐳ() noexcept : buff() {}
            constexpr ᐸCStrTreeUnionᐳ(const ᐸCStrTreeUnionᐳ& other) noexcept = default;
            constexpr ᐸCStrTreeUnionᐳ(const CStrBuff& b) noexcept : buff(b) {}
            constexpr ᐸCStrTreeUnionᐳ(const CStrNode& n) noexcept : node(n) {}
        };
        using CStrTree = ᐸRuntimeᐳ::BoxedUnion<ᐸCStrTreeUnionᐳ>;

        static_assert(sizeof(CStrBuff) == sizeof(CStrNode), "CStrBuff size incorrect");

        constexpr TypeInfoBase g_wellKnownTypeCStrBuff = {
            WELL_KNOWN_TYPE_ID_CSTRBUFF,
            sizeof(CStrBuff),
            byteSizeToSlotCount(sizeof(CStrBuff)),
            LayoutTag::Value, //Note this cheats a bit since we store as pointers in tree but flat in the string!!! Not generally possible for other types.
            BSQ_PTR_MASK_LEAF,
            "CStrBuff",
            nullptr
        };

        constexpr TypeInfoBase g_wellKnownTypeCStrNode = {
            WELL_KNOWN_TYPE_ID_CSTRNODE,
            sizeof(CStrNode),
            byteSizeToSlotCount(sizeof(CStrNode)),
            LayoutTag::Value, //Note this cheats a bit since we store as pointers in tree but flat in the string!!! Not generally possible for other types.
            "0011",
            "CStrNode",
            nullptr
        };

        constexpr TypeInfoBase g_wellKnownTypeCString = {
            WELL_KNOWN_TYPE_ID_CSTRING,
            sizeof(CStrTree),
            byteSizeToSlotCount(sizeof(CStrTree)),
            LayoutTag::Value,
            "20000",
            "CString",
            nullptr
        };
    }

    class CString
    {
    private:
        ᐸRuntimeᐳ::CStrTree tree;

    public:
        constexpr CString() noexcept : tree() {}
        constexpr CString(const ᐸRuntimeᐳ::CStrBuff& b) noexcept : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ᐸCStrTreeUnionᐳ>(&ᐸRuntimeᐳ::g_wellKnownTypeCStrBuff, ᐸRuntimeᐳ::ᐸCStrTreeUnionᐳ(b))) {}
        constexpr CString(const ᐸRuntimeᐳ::CStrNode& n) noexcept : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ᐸCStrTreeUnionᐳ>(&ᐸRuntimeᐳ::g_wellKnownTypeCStrNode, ᐸRuntimeᐳ::ᐸCStrTreeUnionᐳ(n))) {}
        constexpr CString(const ᐸRuntimeᐳ::CStrTree& t) noexcept : tree(t) {}
        constexpr CString(const CString& other) noexcept = default;

        template<size_t len>
        constexpr static CString literal(const char (&cstr)[len]) noexcept
        {
            return CString(ᐸRuntimeᐳ::CStrBuff::literal(cstr));
        }

        size_t size() const noexcept
        {
            return std::bit_cast<ᐸRuntimeᐳ::CStrBase*>(&this->tree)->length;
        }
    };

    class String
    {
        //TODO: yeah todo
    };

    namespace ᐸRuntimeᐳ
    {
        constexpr static CString emptycstr(ᐸRuntimeᐳ::CStrBuff::literal(""));
    }
}

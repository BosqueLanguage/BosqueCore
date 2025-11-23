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

        class CStrBuff
        {
        public:
            constexpr static size_t CSTR_BUFF_SIZE = 16;
            constexpr static size_t CSTR_MAX_SIZE = CSTR_BUFF_SIZE - 1;

            char data[CSTR_BUFF_SIZE];

            constexpr CStrBuff() noexcept : data{0} {}
            constexpr CStrBuff(const CStrBuff& other) noexcept = default;

            template<size_t len>
            constexpr static CStrBuff literal(const char (&cstr)[len]) noexcept
            {
                static_assert(len - 1 <= ᐸRuntimeᐳ::CStrBuff::CSTR_MAX_SIZE, "CString literal too large for CStrBuff");

                CStrBuff cb;
                cb.data[0] = static_cast<char>(len - 1); //store length
                std::copy(cstr, cstr + len - 1, cb.data + 1);

                return cb;
            }

            constexpr size_t size() const noexcept { return static_cast<size_t>(this->data[0]); }
            constexpr char at(size_t index) const noexcept { return this->data[index + 1]; }
        };

        class CStrNode
        {
        public:
            size_t count;
            RColor color;
            CStrTree* left;
            CStrTree* right;

            constexpr CStrNode() noexcept : count(0), color(RColor::Black), left(nullptr), right(nullptr) {}
            constexpr CStrNode(size_t cnt, RColor c, CStrTree* l, CStrTree* r) noexcept : count(cnt), color(c), left(l), right(r) {}
            constexpr CStrNode(const CStrNode& other) noexcept = default;
        };

        union ᐸCStrTreeUnionᐳ
        {
            CStrBuff buff;
            CStrNode* node;

            constexpr ᐸCStrTreeUnionᐳ() noexcept : buff() {}
            constexpr ᐸCStrTreeUnionᐳ(const ᐸCStrTreeUnionᐳ& other) noexcept = default;
            constexpr ᐸCStrTreeUnionᐳ(const CStrBuff& b) noexcept : buff(b) {}
            constexpr ᐸCStrTreeUnionᐳ(CStrNode* n) noexcept : node(n) {}
        };
        using CStrTree = ᐸRuntimeᐳ::BoxedUnion<ᐸCStrTreeUnionᐳ>;

        constexpr TypeInfoBase g_wellKnownTypeCStrBuff = {
            WELL_KNOWN_TYPE_ID_CSTRBUFF,
            sizeof(CStrBuff),
            byteSizeToSlotCount(sizeof(CStrBuff)),
            LayoutTag::Value,
            BSQ_PTR_MASK_LEAF,
            "CStrBuff",
            nullptr
        };

        constexpr TypeInfoBase g_wellKnownTypeCStrNode = {
            WELL_KNOWN_TYPE_ID_CSTRNODE,
            sizeof(CStrNode),
            byteSizeToSlotCount(sizeof(CStrNode)),
            LayoutTag::Ref,
            "0011",
            "CStrNode",
            nullptr
        };

        constexpr TypeInfoBase g_wellKnownTypeCString = {
            WELL_KNOWN_TYPE_ID_CSTRING,
            sizeof(CStrTree),
            byteSizeToSlotCount(sizeof(CStrTree)),
            LayoutTag::Tagged,
            "200",
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
        constexpr CString(ᐸRuntimeᐳ::CStrNode* n) noexcept : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::ᐸCStrTreeUnionᐳ>(&ᐸRuntimeᐳ::g_wellKnownTypeCStrNode, ᐸRuntimeᐳ::ᐸCStrTreeUnionᐳ(n))) {}
        constexpr CString(const ᐸRuntimeᐳ::CStrTree& t) noexcept : tree(t) {}
        constexpr CString(const CString& other) noexcept = default;

        template<size_t len>
        constexpr static CString smliteral(const char (&cstr)[len]) noexcept
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::CStrBuff::CSTR_BUFF_SIZE, "CString literal too large for CStrBuff");
            return CString(ᐸRuntimeᐳ::CStrBuff::literal(cstr));
        }

        size_t size() const noexcept
        {
            if(this->tree.typeinfo->bsqtypeid == ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                return this->tree.data.buff.size();
            }
            else {
                return this->tree.data.node->count;
            }
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

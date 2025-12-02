#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

namespace ᐸRuntimeᐳ
{
    enum class RColor : uint64_t
    {
        Red,
        Black
    };

    class CStrNode;

    class CStrBuff
    {
    public:
        constexpr static size_t CSTR_BUFF_SIZE = 16;
        constexpr static size_t CSTR_MAX_SIZE = CSTR_BUFF_SIZE - 1;

        char data[CSTR_BUFF_SIZE];

        constexpr CStrBuff() : data{0} {}
        constexpr CStrBuff(const CStrBuff& other) = default;

        template<size_t len>
        constexpr static CStrBuff literal(const char (&cstr)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::CStrBuff::CSTR_MAX_SIZE, "CString literal too large for CStrBuff");

            CStrBuff cb;
            cb.data[0] = static_cast<char>(len - 1); //store length
            std::copy(cstr, cstr + len - 1, cb.data + 1);

            return cb;
        }

        constexpr size_t size() const { return static_cast<size_t>(this->data[0]); }
        constexpr char at(size_t index) const { return this->data[index + 1]; }
    };

    union CStrTreeUnion
    {
        CStrBuff buff;
        CStrNode* node;

        constexpr CStrTreeUnion() : buff() {}
        constexpr CStrTreeUnion(const CStrTreeUnion& other) = default;
        constexpr CStrTreeUnion(const CStrBuff& b) : buff(b) {}
        constexpr CStrTreeUnion(CStrNode* n) : node(n) {}
    };
    using CStrTree = ᐸRuntimeᐳ::BoxedUnion<CStrTreeUnion>;

    class CStrNode
    {
    public:
        size_t count;
        RColor color;
        CStrTree* left;
        CStrTree* right;

        constexpr CStrNode() : count(0), color(RColor::Black), left(nullptr), right(nullptr) {}
        constexpr CStrNode(size_t cnt, RColor c, CStrTree* l, CStrTree* r) : count(cnt), color(c), left(l), right(r) {}
        constexpr CStrNode(const CStrNode& other) = default;
    };

    constexpr TypeInfoBase g_typeinfo_CStrBuff = {
        WELL_KNOWN_TYPE_ID_CSTRBUFF,
        sizeof(CStrBuff),
        byteSizeToSlotCount(sizeof(CStrBuff)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "CStrBuff",
        nullptr
    };

    constexpr TypeInfoBase g_typeinfo_CStrNode = {
        WELL_KNOWN_TYPE_ID_CSTRNODE,
        sizeof(CStrNode),
        byteSizeToSlotCount(sizeof(CStrNode)),
        LayoutTag::Ref,
        "0011",
        "CStrNode",
        nullptr
    };

    constexpr TypeInfoBase g_typeinfo_CString = {
        WELL_KNOWN_TYPE_ID_CSTRING,
        sizeof(CStrTree),
        byteSizeToSlotCount(sizeof(CStrTree)),
        LayoutTag::Tagged,
        "200",
        "CString",
        nullptr
    };

    class CString
    {
    private:
        ᐸRuntimeᐳ::CStrTree tree;

    public:
        constexpr CString() : tree() {}
        constexpr CString(const ᐸRuntimeᐳ::CStrBuff& b) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::CStrTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_CStrBuff, ᐸRuntimeᐳ::CStrTreeUnion(b))) {}
        constexpr CString(ᐸRuntimeᐳ::CStrNode* n) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::CStrTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_CStrNode, ᐸRuntimeᐳ::CStrTreeUnion(n))) {}
        constexpr CString(const ᐸRuntimeᐳ::CStrTree& t) : tree(t) {}
        constexpr CString(const CString& other) = default;

        template<size_t len>
        constexpr static CString smliteral(const char (&cstr)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::CStrBuff::CSTR_BUFF_SIZE, "CString literal too large for CStrBuff");
            return CString(ᐸRuntimeᐳ::CStrBuff::literal(cstr));
        }

        size_t size() const
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

    constexpr static CString emptycstr(ᐸRuntimeᐳ::CStrBuff::literal(""));
}

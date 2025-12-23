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

    constexpr TypeInfo g_typeinfo_CStrBuff = {
        WELL_KNOWN_TYPE_ID_CSTRBUFF,
        sizeof(CStrBuff),
        byteSizeToSlotCount(sizeof(CStrBuff)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "CStrBuff",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_CStrNode = {
        WELL_KNOWN_TYPE_ID_CSTRNODE,
        sizeof(CStrNode),
        byteSizeToSlotCount(sizeof(CStrNode)),
        LayoutTag::Ref,
        "0011",
        "CStrNode",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_CString = {
        WELL_KNOWN_TYPE_ID_CSTRING,
        sizeof(CStrTree),
        byteSizeToSlotCount(sizeof(CStrTree)),
        LayoutTag::Tagged,
        "200",
        "CString",
        nullptr
    };

    class XCString
    {
    private:
        ᐸRuntimeᐳ::CStrTree tree;

    public:
        constexpr XCString() : tree() {}
        constexpr XCString(const ᐸRuntimeᐳ::CStrBuff& b) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::CStrTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_CStrBuff, ᐸRuntimeᐳ::CStrTreeUnion(b))) {}
        constexpr XCString(ᐸRuntimeᐳ::CStrNode* n) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::CStrTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_CStrNode, ᐸRuntimeᐳ::CStrTreeUnion(n))) {}
        constexpr XCString(const ᐸRuntimeᐳ::CStrTree& t) : tree(t) {}
        constexpr XCString(const XCString& other) = default;

        template<size_t len>
        constexpr static XCString smliteral(const char (&cstr)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::CStrBuff::CSTR_BUFF_SIZE, "CString literal too large for CStrBuff");
            return XCString(ᐸRuntimeᐳ::CStrBuff::literal(cstr));
        }

        bool empty() const
        {
            return (this->tree.typeinfo->bsqtypeid == ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_CSTRBUFF) && this->tree.data.buff.size() == 0;
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

        size_t bytes() const
        {
            return this->size() * sizeof(char);
        }
    };

    class StrNode;

    class StrBuff
    {
    public:
        constexpr static size_t STR_BUFF_SIZE = 8;
        constexpr static size_t STR_MAX_SIZE = STR_BUFF_SIZE - 1;

        char32_t data[STR_BUFF_SIZE];

        constexpr StrBuff() : data{0} {}
        constexpr StrBuff(const StrBuff& other) = default;

        template<size_t len>
        constexpr static StrBuff literal(const char32_t (&cstr)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::StrBuff::STR_MAX_SIZE, "String literal too large for StrBuff");

            StrBuff sb;
            sb.data[0] = static_cast<char32_t>(len - 1); //store length
            std::copy(cstr, cstr + len - 1, sb.data + 1);
            return sb;
        }

        constexpr size_t size() const { return static_cast<size_t>(this->data[0]); }
        constexpr char32_t at(size_t index) const { return this->data[index + 1]; }
    };

    union StrTreeUnion
    {
        StrBuff buff;
        StrNode* node;

        constexpr StrTreeUnion() : buff() {}
        constexpr StrTreeUnion(const StrTreeUnion& other) = default;
        constexpr StrTreeUnion(const StrBuff& b) : buff(b) {}
        constexpr StrTreeUnion(StrNode* n) : node(n) {}
    };
    using StrTree = ᐸRuntimeᐳ::BoxedUnion<StrTreeUnion>;

    class StrNode
    {
    public:
        size_t count;
        RColor color;
        StrTree* left;
        StrTree* right;

        constexpr StrNode() : count(0), color(RColor::Black), left(nullptr), right(nullptr) {}
        constexpr StrNode(size_t cnt, RColor c, StrTree* l, StrTree* r) : count(cnt), color(c), left(l), right(r) {}
        constexpr StrNode(const StrNode& other) = default;
    };

    constexpr TypeInfo g_typeinfo_StrBuff = {
        WELL_KNOWN_TYPE_ID_CSTRBUFF,
        sizeof(StrBuff),
        byteSizeToSlotCount(sizeof(StrBuff)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "StrBuff",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_StrNode = {
        WELL_KNOWN_TYPE_ID_STRNODE,
        sizeof(StrNode),
        byteSizeToSlotCount(sizeof(StrNode)),
        LayoutTag::Ref,
        "0011",
        "StrNode",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_String = {
        WELL_KNOWN_TYPE_ID_STRING,
        sizeof(StrTree),
        byteSizeToSlotCount(sizeof(StrTree)),
        LayoutTag::Tagged,
        "20000",
        "String",
        nullptr
    };

    class XString
    {
    private:
        ᐸRuntimeᐳ::StrTree tree;

    public:
        constexpr XString() : tree() {}
        constexpr XString(const ᐸRuntimeᐳ::StrBuff& b) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::StrTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_StrBuff, ᐸRuntimeᐳ::StrTreeUnion(b))) {}
        constexpr XString(ᐸRuntimeᐳ::StrNode* n) : tree(ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::StrTreeUnion>(&ᐸRuntimeᐳ::g_typeinfo_StrNode, ᐸRuntimeᐳ::StrTreeUnion(n))) {}
        constexpr XString(const ᐸRuntimeᐳ::StrTree& t) : tree(t) {}
        constexpr XString(const XString& other) = default;

        template<size_t len>
        constexpr static XString smliteral(const char32_t (&cstr)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::StrBuff::STR_MAX_SIZE, "String literal too large for StrBuff");
            return XString(ᐸRuntimeᐳ::StrBuff::literal(cstr));
        }

        bool empty() const
        {
            return (this->tree.typeinfo->bsqtypeid == ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_STRBUFF) && this->tree.data.buff.size() == 0;
        }

        size_t size() const
        {
            if(this->tree.typeinfo->bsqtypeid == ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_STRBUFF) {
                return this->tree.data.buff.size();
            }
            else {
                return this->tree.data.node->count;
            }
        }

        size_t bytes() const
        {
            return this->size() * sizeof(char32_t);
        }
    };

    constexpr static XCString emptycstr(ᐸRuntimeᐳ::CStrBuff::literal(""));
}

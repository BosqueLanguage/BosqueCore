#pragma once

#include "../common.h"
#include "boxed.h"

#define CSTR_BUFF_SIZE 24

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
            char data[CSTR_BUFF_SIZE];

            constexpr CStrBuff() noexcept : CStrBase(0), data{0} {}

            template<size_t len>
            constexpr CStrBuff(const char (&cstr)[len]) noexcept : CStrBase(len - 1), data{0} {
                std::copy(cstr, cstr + len - 1, this->data);
            }

            constexpr CStrBuff(const CStrBuff& other) noexcept = default;
            constexpr CStrBuff& operator=(const CStrBuff& other) noexcept = default;
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
            constexpr CStrNode& operator=(const CStrNode& other) noexcept = default;
        };

        union CStrTreeᐤUnion
        {
            CStrBuff buff;
            CStrNode node;

            constexpr CStrTreeᐤUnion() noexcept : buff() {}
            constexpr CStrTreeᐤUnion(const CStrBuff& b) noexcept : buff(b) {}
            constexpr CStrTreeᐤUnion(const CStrNode& n) noexcept : node(n) {}

            constexpr CStrTreeᐤUnion(const CStrTreeᐤUnion& other) noexcept = default;
            constexpr CStrTreeᐤUnion& operator=(const CStrTreeᐤUnion& other) noexcept = default;
        };
        using CStrTree = ᐸRuntimeᐳ::BoxedUnion<CStrTreeᐤUnion>;

        static_assert(sizeof(CStrBuff) == sizeof(CStrNode), "CStrBuff size incorrect");

        constexpr TypeInfoBase g_wellKnownTypeCStrBuff = {
            WELL_KNOWN_TYPE_ID_CSTRBUFF,
            sizeof(CStrBuff),
            sizeof(CStrBuff) / BSQ_SLOT_BYTE_SIZE,
            LayoutTag::Value, //Note this cheats a bit since we store as pointers in tree but flat in the string!!! Not generally possible for other types.
            PTR_MASK_LEAF,
            "CStrBuff",
            nullptr
        };

        constexpr TypeInfoBase g_wellKnownTypeCStrNode = {
            WELL_KNOWN_TYPE_ID_CSTRNODE,
            sizeof(CStrNode),
            sizeof(CStrNode) / BSQ_SLOT_BYTE_SIZE,
            LayoutTag::Value, //Note this cheats a bit since we store as pointers in tree but flat in the string!!! Not generally possible for other types.
            "0011",
            "CStrNode",
            nullptr
        };

        constexpr TypeInfoBase g_wellKnownTypeCString = {
            WELL_KNOWN_TYPE_ID_CSTRING,
            sizeof(CStrTree),
            sizeof(CStrTree) / BSQ_SLOT_BYTE_SIZE,
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
        constexpr CString(ᐸRuntimeᐳ::CStrBuff b) noexcept : tree(ᐸRuntimeᐳ::Boxed<sizeof(ᐸRuntimeᐳ::CStrBuff) / BSQ_SLOT_BYTE_SIZE>::makeBoxed<ᐸRuntimeᐳ::CStrBuff>(&ᐸRuntimeᐳ::g_wellKnownTypeCStrBuff, b)) {}
        constexpr CString(const ᐸRuntimeᐳ::CStrTree& t) noexcept : tree(t) {}

        constexpr static CString foo() noexcept {
            constexpr auto t = &ᐸRuntimeᐳ::g_wellKnownTypeCStrBuff;
            constexpr ᐸRuntimeᐳ::CStrBuff b("hello");

            constexpr auto bs = ᐸRuntimeᐳ::CStrTreeᐤUnion(b);
            constexpr auto bb = ᐸRuntimeᐳ::BoxedUnion<ᐸRuntimeᐳ::CStrTreeᐤUnion>(&ᐸRuntimeᐳ::g_wellKnownTypeCStrBuff, bs);

            
            ᐸRuntimeᐳ::CStrTree t1;
            t1 = bb;

            return CString(b);
        }

        constexpr CString(const CString& other) noexcept = default;
        constexpr CString& operator=(const CString& other) noexcept = default;

        static constexpr CString emptycstr(&g_wellKnownTypeCString);
    };

    class String
    {

    };
}

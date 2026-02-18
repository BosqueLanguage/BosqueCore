#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

#include "postree.h"

namespace ᐸRuntimeᐳ
{
    class CStrRootInlineContent
    {
    public:
        constexpr static size_t CSTR_BUFF_SIZE = 16;
        constexpr static size_t CSTR_MAX_SIZE = CSTR_BUFF_SIZE - 1;

        char data[CSTR_BUFF_SIZE];

        constexpr CStrRootInlineContent() : data{0} {}
        constexpr CStrRootInlineContent(const CStrRootInlineContent& other) = default;

        constexpr bool empty() const { return static_cast<size_t>(this->data[0]) == 0; }

        template<size_t len>
        constexpr static CStrRootInlineContent literal(const char (&cstr)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::CStrRootInlineContent::CSTR_MAX_SIZE, "CString literal too large for CStrRootInlineContent");

            CStrRootInlineContent cb;
            cb.data[0] = static_cast<char>(len - 1); //store length
            std::copy(cstr, cstr + len - 1, cb.data + 1);

            return cb;
        }

        constexpr size_t size() const { return static_cast<size_t>(this->data[0]); }
        constexpr char at(size_t index) const { return this->data[index + 1]; }

        constexpr static CStrRootInlineContent create_empty() { return CStrRootInlineContent(); }
    };

    class CStrRootTreeContent
    {
    public:
        constexpr static size_t CSTR_MAX_LEAF_SIZE = CStrRootInlineContent::CSTR_BUFF_SIZE * 2;

        PosRBTree<char, CSTR_MAX_LEAF_SIZE>* postree;
    };

    union CStrTreeUnion
    {
        CStrRootInlineContent inlinecstr;
        CStrRootTreeContent treecstr;

        constexpr CStrTreeUnion() : inlinecstr() {}
        constexpr CStrTreeUnion(const CStrTreeUnion& other) = default;
        constexpr CStrTreeUnion(const CStrRootInlineContent& c) : inlinecstr(c) {}
        constexpr CStrTreeUnion(const CStrRootTreeContent& c) : treecstr(c) {}
    };

    constexpr TypeInfo g_typeinfo_CStrTreeLeaf = {
        WELL_KNOWN_TYPE_ID_CSTR_TREE_LEAF,
        sizeof(PosRBTreeTag) + sizeof(PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>),
        byteSizeToSlotCount(sizeof(PosRBTreeTag) + sizeof(PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>)),
        LayoutTag::Ref,
        BSQ_PTR_MASK_LEAF,
        "CStrTreeLeaf",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_CStrTreeNode = {
        WELL_KNOWN_TYPE_ID_CSTR_TREE_NODE,
        sizeof(PosRBTreeTag) + sizeof(PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>),
        byteSizeToSlotCount(sizeof(PosRBTreeTag) + sizeof(PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>)),
        LayoutTag::Ref,
        "00011",
        "CStrTreeNode",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_CStrInline = {
        WELL_KNOWN_TYPE_ID_CSTR_INLINE,
        sizeof(CStrRootInlineContent),
        byteSizeToSlotCount(sizeof(CStrRootInlineContent)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "CStrInline",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_CStrTree = {
        WELL_KNOWN_TYPE_ID_CSTR_TREE,
        sizeof(CStrRootTreeContent),
        byteSizeToSlotCount(sizeof(CStrRootTreeContent)),
        LayoutTag::Value,
        "1",
        "CStrTree",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_CString = {
        WELL_KNOWN_TYPE_ID_CSTRING,
        sizeof(BoxedUnion<CStrTreeUnion>),
        byteSizeToSlotCount(sizeof(BoxedUnion<CStrTreeUnion>)),
        LayoutTag::Tagged,
        "200",
        "CString",
        nullptr
    };

    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    class XCStringIterator
    {
    public:
        int64_t index;
        BoxedUnion<CStrTreeUnion> tree;

        using value_type = char;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            if(this->tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTR_INLINE) {
                return this->tree.data.inlinecstr.at(this->index);
            }
            else {
                return this->tree.data.treecstr.postree->get(this->index);
            }
        }

        XCStringIterator& operator++()
        {
            this->index++;
            return *this;
        }
 
        XCStringIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        XCStringIterator& operator--()
        {
            this->index--;
            return *this;
        }
 
        XCStringIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const XCStringIterator& lhs, const XCStringIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XCStringIterator& lhs, const XCStringIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };
    static_assert(std::bidirectional_iterator<XCStringIterator>);

    class XCString
    {
    private:
        BoxedUnion<CStrTreeUnion> tree;

    public:
        constexpr XCString() : tree() {}
        constexpr XCString(const CStrRootInlineContent& b) : tree(BoxedUnion<CStrTreeUnion>(&g_typeinfo_CStrInline, CStrTreeUnion(b))) {}
        constexpr XCString(CStrRootTreeContent& n) : tree(BoxedUnion<CStrTreeUnion>(&g_typeinfo_CStrTree, CStrTreeUnion(n))) {}
        constexpr XCString(const XCString& other) = default;

        template<size_t len>
        constexpr static XCString smliteral(const char (&cstr)[len])
        {
            static_assert(len - 1 <= CStrRootInlineContent::CSTR_MAX_SIZE, "CString literal too large for CStrRootInlineContent");
            return XCString(CStrRootInlineContent::literal(cstr));
        }

        bool empty() const
        {
            return (this->tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTR_INLINE) && this->tree.data.inlinecstr.size() == 0;
        }

        size_t size() const
        {
            if(this->tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTR_INLINE) {
                return this->tree.data.inlinecstr.size();
            }
            else {
                return this->tree.data.treecstr.postree->count();
            }
        }

        size_t bytes() const
        {
            return this->size() * sizeof(char);
        }

        XCStringIterator begin() const
        {
            return XCStringIterator{0, this->tree};
        }

        XCStringIterator end() const
        {
            return XCStringIterator{(int64_t)this->size(), this->tree};
        }

        friend XBool operator==(const XCString& lhs, const XCString& rhs) 
        { 
            return XBool::from(std::equal(lhs.begin(), lhs.end(), rhs.begin())); 
        }

        friend XBool operator<(const XCString& lhs, const XCString& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                auto mmpos = std::mismatch(lhs.begin(), lhs.end(), rhs.begin());
                if(mmpos.first == lhs.end()) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first < *mmpos.second);
                }
            }
        }

        friend XBool operator>(const XCString& lhs, const XCString& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() > rhs.size());
            }
            else {
                auto mmpos = std::mismatch(lhs.begin(), lhs.end(), rhs.begin());
                if(mmpos.first == lhs.end()) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first > *mmpos.second);
                } 
            } 
        }
        
        friend XBool operator!=(const XCString& lhs, const XCString& rhs) { return !(lhs == rhs); }
        friend XBool operator<=(const XCString& lhs, const XCString& rhs) { return !(lhs > rhs); }
        friend XBool operator>=(const XCString& lhs, const XCString& rhs) { return !(lhs < rhs); }
    };

    template<size_t K>
    class XFCStringRepr 
    {
    public:
        const char* strcomps[K];
        bool hasprefix;
        bool hassuffix;

        size_t cmpsize;
        size_t fcid;
    };

    class XFCString
    {
    public:
        size_t fcid;

        template<size_t K>
        static XCString interpolate(XFCStringRepr<K>* repr, XCString (&cstr)[K])
        {
            size_t total_size = repr->cmpsize;
            for(size_t i = 0; i < K; i++) {
                total_size += cstr[i].size();
            }

            if(total_size <= CStrRootInlineContent::CSTR_MAX_SIZE) {
                char inlined[total_size + 1] = {0};
                
                xxxx;
                
                return XCString::smliteral(inlined);
            }
            else {
                assert(false); // Not Implemented: full support for FString interpolation
            }
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

        constexpr bool empty() const { return static_cast<size_t>(this->data[0]) == 0; }

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

        constexpr static StrBuff create_empty() { return StrBuff(); }
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
    using StrTree = BoxedUnion<StrTreeUnion>;

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
        WELL_KNOWN_TYPE_ID_STRBUFF,
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

    class XStringIterator
    {
    private:
        int64_t buffidx;
        StrBuff currbuff;

        int64_t index;
        StrTree currtree;

        constexpr XStringIterator(int64_t idx, StrBuff currbuff, int64_t index, StrTree currtree) : buffidx(idx), currbuff(currbuff), index(index), currtree(currtree) {}

        void incrementSlow()
        {        
            if(this->currtree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for String trees
            }
        }

        void decrementSlow()
        {        
            if(this->currtree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for String trees
            }
        }

    public:
        using value_type = char32_t;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag; 

        using pointer = value_type*;
        using reference = value_type&;

        XStringIterator(): buffidx(0), currbuff(), index(0), currtree() {}
        XStringIterator(const XStringIterator& other) = default;

        static XStringIterator initializeBegin(StrTree tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                return XStringIterator(0, tree.data.buff, 0, tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        static XStringIterator initializeEnd(StrTree tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                return XStringIterator(tree.data.buff.size(), tree.data.buff, tree.data.buff.size(), tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        value_type operator*() const 
        { 
            return this->currbuff.at(this->buffidx); 
        }

        XStringIterator& operator++()
        {
            this->index++;
            this->buffidx++;
            if(this->buffidx >= (int64_t)this->currbuff.size()) {
                this->incrementSlow();
            }

            return *this;
        }
 
        XStringIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        XStringIterator& operator--()
        {
            this->index--;
            this->buffidx--;
            if(this->buffidx < 0) {
                this->decrementSlow();
            }

            return *this;
        }
 
        XStringIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const XStringIterator& lhs, const XStringIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XStringIterator& lhs, const XStringIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };
    static_assert(std::bidirectional_iterator<XStringIterator>);

    class XString
    {
    private:
        ᐸRuntimeᐳ::StrTree tree;

    public:
        constexpr XString() : tree() {}
        constexpr XString(const StrBuff& b) : tree(BoxedUnion<StrTreeUnion>(&g_typeinfo_StrBuff, StrTreeUnion(b))) {}
        constexpr XString(StrNode* n) : tree(BoxedUnion<StrTreeUnion>(&g_typeinfo_StrNode, StrTreeUnion(n))) {}
        constexpr XString(const StrTree& t) : tree(t) {}
        constexpr XString(const XString& other) = default;

        template<size_t len>
        constexpr static XString smliteral(const char32_t (&cstr)[len])
        {
            static_assert(len - 1 <= StrBuff::STR_MAX_SIZE, "String literal too large for StrBuff");
            return XString(StrBuff::literal(cstr));
        }

        bool empty() const
        {
            return (this->tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) && this->tree.data.buff.size() == 0;
        }

        size_t size() const
        {
            if(this->tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
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

        XStringIterator begin() const
        {
            return XStringIterator::initializeBegin(this->tree);
        }

        XStringIterator end() const
        {
            return XStringIterator::initializeEnd(this->tree);
        }

        friend XBool operator==(const XString& lhs, const XString& rhs) 
        { 
            XStringIterator lhsit = lhs.begin();
            XStringIterator elhsit = lhs.end();

            XStringIterator rhsit = rhs.begin();

            return XBool::from(std::equal(lhsit, elhsit, rhsit)); 
        }

        friend XBool operator<(const XString& lhs, const XString& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                XStringIterator lhsit = lhs.begin();
                XStringIterator elhsit = lhs.end(); 

                XStringIterator rhsit = rhs.begin();

                auto mmpos = std::mismatch(lhsit, elhsit, rhsit);
                if(mmpos.first == elhsit) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first < *mmpos.second);
                }
            }
        }

        friend XBool operator>(const XString& lhs, const XString& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() > rhs.size());
            }
            else {
                XStringIterator lhsit = lhs.begin();
                XStringIterator elhsit = lhs.end(); 

                XStringIterator rhsit = rhs.begin();

                auto mmpos = std::mismatch(lhsit, elhsit, rhsit);
                if(mmpos.first == elhsit) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first > *mmpos.second);
                } 
            } 
        }
        
        friend XBool operator!=(const XString& lhs, const XString& rhs) { return !(lhs == rhs); }
        friend XBool operator<=(const XString& lhs, const XString& rhs) { return !(lhs > rhs); }
        friend XBool operator>=(const XString& lhs, const XString& rhs) { return !(lhs < rhs); }
    };

    constexpr static XCString emptycstr(CStrRootInlineContent::literal(""));
    constexpr static XString emptystr(StrBuff::literal(U""));
}

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

    template<typename T>
    class IterStack
    {
    private:
        std::array<T, 32> data;
        int64_t top;

    public:
        constexpr IterStack() : data{}, top(0) {}
        constexpr IterStack(const IterStack& other) = default;

        constexpr bool empty() const { return this->top == 0; }
        constexpr size_t size() const { return static_cast<size_t>(this->top); }

        constexpr void push(const T& value) 
        { 
            this->data[this->top] = value;
            this->top++;
        }

        constexpr T pop() 
        { 
            this->top--;
            return this->data[this->top];
        }
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

        constexpr bool empty() const { return static_cast<size_t>(this->data[0]) == 0; }

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

        constexpr static CStrBuff create_empty() { return CStrBuff(); }
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
    using CStrTree = BoxedUnion<CStrTreeUnion>;

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

    class XCStringInputIterator
    {
    private:
        int64_t buffidx;
        CStrBuff currbuff;

        int64_t index;
        IterStack<CStrNode*>* treestack;

        constexpr XCStringInputIterator(int64_t buffidx, CStrBuff currbuff, int64_t index, IterStack<CStrNode*>* treestack) : buffidx(buffidx), currbuff(currbuff), index(index), treestack(treestack) {}

        void advanceSlow()
        {
            if(!this->treestack->empty()) {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

    public:
        using value_type = char;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::input_iterator_tag; 

        using pointer = value_type*;
        using reference = value_type&;

        static XCStringInputIterator initializeBegin(CStrTree tree, IterStack<CStrNode*>* treestack)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                return XCStringInputIterator(0, tree.data.buff, 0, treestack);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        static XCStringInputIterator initializeEnd(CStrTree tree, IterStack<CStrNode*>* treestack)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                return XCStringInputIterator(tree.data.buff.size(), tree.data.buff, tree.data.buff.size(), treestack);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        value_type operator*() const 
        { 
            return this->currbuff.at(this->buffidx); 
        }

        XCStringInputIterator& operator++()
        {
            this->index++;
            this->buffidx++;
            if(this->buffidx >= (int64_t)this->currbuff.size()) {
                this->advanceSlow();
            }

            return *this;
        }
 
        void operator++(int)
        {
            ++*this;
        }

        friend bool operator==(const XCStringInputIterator& lhs, const XCStringInputIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XCStringInputIterator& lhs, const XCStringInputIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };
    static_assert(std::input_iterator<XCStringInputIterator>);

    class XCStringBidiIterator
    {
    private:
        int64_t buffidx;
        CStrBuff currbuff;

        int64_t index;
        CStrTree* currtree;

        constexpr XCStringBidiIterator(int64_t idx, CStrBuff currbuff, int64_t index, CStrTree* currtree) : buffidx(idx), currbuff(currbuff), index(index), currtree(currtree) {}

        void incrementSlow()
        {        
            if(this->currtree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        void decrementSlow()
        {        
            if(this->currtree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

    public:
        using value_type = char;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        XCStringBidiIterator(): buffidx(0), currbuff(), index(0), currtree(nullptr) {}
        XCStringBidiIterator(const XCStringBidiIterator& other) = default;

        static XCStringBidiIterator initializeBegin(CStrTree* tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                return XCStringBidiIterator(0, tree->data.buff, 0, tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        static XCStringBidiIterator initializeEnd(CStrTree* tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                return XCStringBidiIterator(tree->data.buff.size(), tree->data.buff, tree->data.buff.size(), tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        value_type operator*() const 
        { 
            return this->currbuff.at(this->buffidx); 
        }

        XCStringBidiIterator& operator++()
        {
            this->index++;
            this->buffidx++;
            if(this->buffidx >= (int64_t)this->currbuff.size()) {
                this->incrementSlow();
            }

            return *this;
        }
 
        XCStringBidiIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        XCStringBidiIterator& operator--()
        {
            this->index--;
            this->buffidx--;
            if(this->buffidx < 0) {
                this->decrementSlow();
            }

            return *this;
        }
 
        XCStringBidiIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const XCStringBidiIterator& lhs, const XCStringBidiIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XCStringBidiIterator& lhs, const XCStringBidiIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };
    static_assert(std::bidirectional_iterator<XCStringBidiIterator>);

    class XCString
    {
    private:
        CStrTree tree;

    public:
        constexpr XCString() : tree() {}
        constexpr XCString(const CStrBuff& b) : tree(BoxedUnion<CStrTreeUnion>(&g_typeinfo_CStrBuff, CStrTreeUnion(b))) {}
        constexpr XCString(CStrNode* n) : tree(BoxedUnion<CStrTreeUnion>(&g_typeinfo_CStrNode, CStrTreeUnion(n))) {}
        constexpr XCString(const CStrTree& t) : tree(t) {}
        constexpr XCString(const XCString& other) = default;

        template<size_t len>
        constexpr static XCString smliteral(const char (&cstr)[len])
        {
            static_assert(len - 1 <= CStrBuff::CSTR_BUFF_SIZE, "CString literal too large for CStrBuff");
            return XCString(CStrBuff::literal(cstr));
        }

        bool empty() const
        {
            return (this->tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) && this->tree.data.buff.size() == 0;
        }

        size_t size() const
        {
            if(this->tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
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

        XCStringInputIterator input_iterator_begin(IterStack<CStrNode*>* treestack) const
        {
            return XCStringInputIterator::initializeBegin(this->tree, treestack);
        }

        XCStringInputIterator input_iterator_end(IterStack<CStrNode*>* treestack) const
        {
            return XCStringInputIterator::initializeEnd(this->tree, treestack);
        }

        friend XBool operator==(const XCString& lhs, const XCString& rhs) 
        { 
            IterStack<CStrNode*> lhsits;
            XCStringInputIterator lhsit = lhs.input_iterator_begin(&lhsits);

            IterStack<CStrNode*> elhsits;
            XCStringInputIterator elhsit = lhs.input_iterator_end(&elhsits);

            IterStack<CStrNode*> rhsits;
            XCStringInputIterator rhsit = rhs.input_iterator_begin(&rhsits);

            return XBool::from(std::equal(lhsit, elhsit, rhsit)); 
        }

        friend XBool operator<(const XCString& lhs, const XCString& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                IterStack<CStrNode*> lhsits;
                XCStringInputIterator lhsit = lhs.input_iterator_begin(&lhsits);

                IterStack<CStrNode*> elhsits;
                XCStringInputIterator elhsit = lhs.input_iterator_end(&elhsits);

                IterStack<CStrNode*> rhsits;
                XCStringInputIterator rhsit = rhs.input_iterator_begin(&rhsits);

                auto mmpos = std::mismatch(lhsit, elhsit, rhsit);
                if(mmpos.first == elhsit) {
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
                IterStack<CStrNode*> lhsits;
                XCStringInputIterator lhsit = lhs.input_iterator_begin(&lhsits);

                IterStack<CStrNode*> elhsits;
                XCStringInputIterator elhsit = lhs.input_iterator_end(&elhsits);

                IterStack<CStrNode*> rhsits;
                XCStringInputIterator rhsit = rhs.input_iterator_begin(&rhsits);

                auto mmpos = std::mismatch(lhsit, elhsit, rhsit);
                if(mmpos.first == elhsit) {
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

    class XStringInputIterator
    {
    private:
        int64_t buffidx;
        StrBuff currbuff;

        int64_t index;
        IterStack<StrNode*>* treestack;

        constexpr XStringInputIterator(int64_t buffidx, StrBuff currbuff, int64_t index, IterStack<StrNode*>* treestack) : buffidx(buffidx), currbuff(currbuff), index(index), treestack(treestack) {}

        void advanceSlow()
        {
            if(!this->treestack->empty()) {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

    public:
        using value_type = char32_t;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::input_iterator_tag; 

        using pointer = value_type*;
        using reference = value_type&;

        static XStringInputIterator initializeBegin(StrTree tree, IterStack<StrNode*>* treestack)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                return XStringInputIterator(0, tree.data.buff, 0, treestack);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        static XStringInputIterator initializeEnd(StrTree tree, IterStack<StrNode*>* treestack)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                return XStringInputIterator(tree.data.buff.size(), tree.data.buff, tree.data.buff.size(), treestack);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        value_type operator*() const 
        { 
            return this->currbuff.at(this->buffidx); 
        }

        XStringInputIterator& operator++()
        {
            this->index++;
            this->buffidx++;
            if(this->buffidx >= (int64_t)this->currbuff.size()) {
                this->advanceSlow();
            }

            return *this;
        }
 
        void operator++(int)
        {
            ++*this;
        }

        friend bool operator==(const XStringInputIterator& lhs, const XStringInputIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XStringInputIterator& lhs, const XStringInputIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };
    static_assert(std::input_iterator<XStringInputIterator>);

    class XStringBidiIterator
    {
    private:
        int64_t buffidx;
        StrBuff currbuff;

        int64_t index;
        StrTree* currtree;

        constexpr XStringBidiIterator(int64_t idx, StrBuff currbuff, int64_t index, StrTree* currtree) : buffidx(idx), currbuff(currbuff), index(index), currtree(currtree) {}

        void incrementSlow()
        {        
            if(this->currtree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        void decrementSlow()
        {        
            if(this->currtree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_CSTRBUFF) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

    public:
        using value_type = char32_t;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag; 

        using pointer = value_type*;
        using reference = value_type&;


        XStringBidiIterator(): buffidx(0), currbuff(), index(0), currtree(nullptr) {}
        XStringBidiIterator(const XStringBidiIterator& other) = default;

        static XStringBidiIterator initializeBegin(StrTree* tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                return XStringBidiIterator(0, tree->data.buff, 0, tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        static XStringBidiIterator initializeEnd(StrTree* tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree->typeinfo->bsqtypeid == WELL_KNOWN_TYPE_ID_STRBUFF) {
                return XStringBidiIterator(tree->data.buff.size(), tree->data.buff, tree->data.buff.size(), tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        value_type operator*() const 
        { 
            return this->currbuff.at(this->buffidx); 
        }

        XStringBidiIterator& operator++()
        {
            this->index++;
            this->buffidx++;
            if(this->buffidx >= (int64_t)this->currbuff.size()) {
                this->incrementSlow();
            }

            return *this;
        }
 
        XStringBidiIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        XStringBidiIterator& operator--()
        {
            this->index--;
            this->buffidx--;
            if(this->buffidx < 0) {
                this->decrementSlow();
            }

            return *this;
        }
 
        XStringBidiIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const XStringBidiIterator& lhs, const XStringBidiIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XStringBidiIterator& lhs, const XStringBidiIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };
    static_assert(std::bidirectional_iterator<XStringBidiIterator>);

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

        XStringInputIterator input_iterator_begin(IterStack<StrNode*>* treestack) const
        {
            return XStringInputIterator::initializeBegin(this->tree, treestack);
        }

        XStringInputIterator input_iterator_end(IterStack<StrNode*>* treestack) const
        {
            return XStringInputIterator::initializeEnd(this->tree, treestack);
        }

        friend XBool operator==(const XString& lhs, const XString& rhs) 
        { 
            IterStack<StrNode*> lhsits;
            XStringInputIterator lhsit = lhs.input_iterator_begin(&lhsits);

            IterStack<StrNode*> elhsits;
            XStringInputIterator elhsit = lhs.input_iterator_end(&elhsits);

            IterStack<StrNode*> rhsits;
            XStringInputIterator rhsit = rhs.input_iterator_begin(&rhsits);

            return XBool::from(std::equal(lhsit, elhsit, rhsit)); 
        }

        friend XBool operator<(const XString& lhs, const XString& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                IterStack<StrNode*> lhsits;
                XStringInputIterator lhsit = lhs.input_iterator_begin(&lhsits);

                IterStack<StrNode*> elhsits;
                XStringInputIterator elhsit = lhs.input_iterator_end(&elhsits);

                IterStack<StrNode*> rhsits;
                XStringInputIterator rhsit = rhs.input_iterator_begin(&rhsits);

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
                IterStack<StrNode*> lhsits;
                XStringInputIterator lhsit = lhs.input_iterator_begin(&lhsits);

                IterStack<StrNode*> elhsits;
                XStringInputIterator elhsit = lhs.input_iterator_end(&elhsits);

                IterStack<StrNode*> rhsits;
                XStringInputIterator rhsit = rhs.input_iterator_begin(&rhsits);

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

    constexpr static XCString emptycstr(CStrBuff::literal(""));
    constexpr static XString emptystr(StrBuff::literal(U""));
}

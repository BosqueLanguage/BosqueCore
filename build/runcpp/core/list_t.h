#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

namespace ᐸRuntimeᐳ
{
    constexpr static size_t MAX_LIST_INLINE_BYTES = 64; //Bytes

    constexpr size_t LIST_T_CAPACITY(size_t elem_size)
    {
        return std::max((MAX_LIST_INLINE_BYTES - sizeof(size_t)) / elem_size, (size_t)1);
    }

    template<typename T>
    class ListTInlineNode;

    //Inline buffer for small inline values (under 64 bytes total size)
    template<typename T>
    class ListTInlineBuff
    {
    public:
        T data[LIST_T_CAPACITY(sizeof(T))];
        size_t count;

        static TypeInfo* s_typeinfo;

        constexpr ListTInlineBuff() : data{0}, count(0) {}
        constexpr ListTInlineBuff(const ListTInlineBuff& other) = default;
        constexpr bool empty() const { return this->count== 0; }

        template<size_t len>
        constexpr static ListTInlineBuff literal(const T (&elems)[len])
        {
            static_assert(len <= LIST_T_CAPACITY(sizeof(T)), "Literal too large for ListTInlineBuff");

            ListTInlineBuff cb;
            std::copy(elems, elems + len, cb.data);
            cb.count = len;

            return cb;
        }

        constexpr size_t size() const { return this->count; }
        constexpr T at(size_t index) const { return this->data[index]; }

        constexpr static ListTInlineBuff create_empty() { return ListTInlineBuff(); }
    };

    template<typename T>
    union ListTTreeUnion
    {
        ListTInlineBuff<T> buff;
        ListTInlineNode<T>* node;

        constexpr ListTTreeUnion() : buff() {}
        constexpr ListTTreeUnion(const ListTTreeUnion& other) = default;
        constexpr ListTTreeUnion(const ListTInlineBuff<T>& b) : buff(b) {}
        constexpr ListTTreeUnion(ListTInlineNode<T>* n) : node(n) {}
    };
    template<typename T>    
    using ListTTree = BoxedUnion<ListTTreeUnion<T>>;

    template<typename T>
    class ListTInlineNode
    {
    public:
        size_t count;
        RColor color;
        ListTTree<T>* left;
        ListTTree<T>* right;

        static TypeInfo* s_typeinfo;

        constexpr ListTInlineNode() : count(0), color(RColor::Black), left(nullptr), right(nullptr) {}
        constexpr ListTInlineNode(size_t cnt, RColor c, ListTTree<T>* l, ListTTree<T>* r) : count(cnt), color(c), left(l), right(r) {}
        constexpr ListTInlineNode(const ListTInlineNode& other) = default;
    };

    template<typename T>
    constexpr TypeInfo g_typeinfo_ListTInlineBuff_generate(size_t id, const char* mask, const char* name) {
        return {
            id,
            sizeof(ListTInlineBuff<T>),
            byteSizeToSlotCount(sizeof(ListTInlineBuff<T>)),
            LayoutTag::Value,
            mask,
            name,
            nullptr
        };
    }

    template<typename T>
    constexpr TypeInfo g_typeinfo_ListTNode_generate(size_t id, const char* name) {
        return {
            id,
            sizeof(ListTInlineNode<T>),
            byteSizeToSlotCount(sizeof(ListTInlineNode<T>)),
            LayoutTag::Ref,
            "0011",
            name,
            nullptr
        };
    }

    template<typename T>
    constexpr TypeInfo g_typeinfo_ListTTree_generate(size_t id, const char* mask, const char* name) {
        return {
            id,
            sizeof(ListTTree<T>),
            byteSizeToSlotCount(sizeof(ListTTree<T>)),
            LayoutTag::Tagged,
            mask,
            name,
            nullptr
        };
    }

    template<typename T>
    class XListTIterator
    {
    private:
        int64_t buffidx;
        ListTInlineBuff<T>  currbuff;

        int64_t index;
        ListTTree<T> currtree;

        constexpr XListTIterator(int64_t idx, ListTInlineBuff<T> currbuff, int64_t index, ListTTree<T> currtree) : buffidx(idx), currbuff(currbuff), index(index), currtree(currtree) {}

        void incrementSlow()
        {        
            if(this->currtree.typeinfo == ListTInlineBuff<T>::s_typeinfo) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        void decrementSlow()
        {        
            if(this->currtree.typeinfo == ListTInlineBuff<T>::s_typeinfo) {
                this->buffidx = this->index;
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

    public:
        using value_type = T;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        XListTIterator(): buffidx(0), currbuff(), index(0), currtree() {}
        XListTIterator(const XListTIterator& other) = default;

        static XListTIterator initializeBegin(ListTTree<T> tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo == ListTInlineBuff<T>::s_typeinfo) {
                return XListTIterator(0, tree.data.buff, 0, tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        static XListTIterator initializeEnd(ListTTree<T> tree)
        {
            //Handle empty iterator or small iterator as special case
            if(tree.typeinfo == ListTInlineBuff<T>::s_typeinfo) {
                return XListTIterator(tree.data.buff.size(), tree.data.buff, tree.data.buff.size(), tree);
            }
            else {
                assert(false); // Not Implemented: full iterator for CString trees
            }
        }

        value_type operator*() const 
        { 
            return this->currbuff.at(this->buffidx); 
        }

        XListTIterator& operator++()
        {
            this->index++;
            this->buffidx++;
            if(this->buffidx >= (int64_t)this->currbuff.size()) {
                this->incrementSlow();
            }

            return *this;
        }
 
        XListTIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        XListTIterator& operator--()
        {
            this->index--;
            this->buffidx--;
            if(this->buffidx < 0) {
                this->decrementSlow();
            }

            return *this;
        }
 
        XListTIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const XListTIterator& lhs, const XListTIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XListTIterator& lhs, const XListTIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };

    template<typename T>
    class XList
    {
    private:
        ᐸRuntimeᐳ::ListTTree<T> tree;

    public:
        constexpr XList() : tree() {}
        constexpr XList(const ListTInlineBuff<T>& b) : tree(BoxedUnion<ListTTreeUnion>(ListTInlineBuff<T>::s_typeinfo, ListTTreeUnion(b))) {}
        constexpr XList(ListTInlineNode<T>* n) : tree(BoxedUnion<ListTTreeUnion>(ListTInlineNode<T>::s_typeinfo, ListTTreeUnion(n))) {}
        constexpr XList(const ListTTree<T>& t) : tree(t) {}
        constexpr XList(const XList& other) = default;

        template<size_t len>
        constexpr static XList smliteral(const T (&cdata)[len])
        {
            static_assert(len <= LIST_T_CAPACITY(sizeof(T)), "List literal too large for ListTInlineBuff");
            return XList(ListTInlineBuff<T>::literal(cdata));
        }

        bool empty() const
        {
            return (this->tree.typeinfo == XList::InlineTypeInfo) && this->tree.data.buff.count == 0;
        }

        size_t size() const
        {
            if(this->tree.typeinfo == XList::InlineTypeInfo) {
                return this->tree.data.buff.count;
            }
            else {
                return this->tree.data.node->count;
            }
        }

        XListTIterator<T> begin() const
        {
            return XListTIterator<T>::initializeBegin(this->tree);
        }

        XListTIterator<T> end() const
        {
            return XListTIterator<T>::initializeEnd(this->tree);
        }
    };

    //TODO -- dummy instantiation to provide quick compile time check -- can remove later once we are a bit more confident
    using XListTest_IntList = XListTIterator<int64_t>;
    static_assert(std::bidirectional_iterator<XListTIterator<int64_t>>);

    using XIntList = XList<int64_t>;
}

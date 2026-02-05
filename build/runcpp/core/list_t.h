#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

namespace ᐸRuntimeᐳ
{
    constexpr static size_t MAX_LIST_INLINE_BYTES = 48; //Bytes -- so 64 total when we add 8 bytes for the size and 8 bytes for the tag or 1 element of the value type if larger!!!

    constexpr size_t LIST_T_CAPACITY(size_t elem_size)
    {
        return std::max((MAX_LIST_INLINE_BYTES - sizeof(size_t)) / elem_size, (size_t)1);
    }

    template<typename T>
    class ListTNode;

    //Inline buffer for small inline values (under 56 bytes total size)
    template<typename T>
    class ListTInlineBuff
    {
    public:
        T data[LIST_T_CAPACITY(sizeof(T))];
        size_t count;

        static const TypeInfo* s_typeinfo;

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
        ListTNode<T>* node;

        constexpr ListTTreeUnion() : buff() {}
        constexpr ListTTreeUnion(const ListTTreeUnion& other) = default;
        constexpr ListTTreeUnion(const ListTInlineBuff<T>& b) : buff(b) {}
        constexpr ListTTreeUnion(ListTNode<T>* n) : node(n) {}
    };
    template<typename T>    
    using ListTTree = BoxedUnion<ListTTreeUnion<T>>;

    template<typename T>
    class ListTNode
    {
    public:
        size_t count;
        RColor color;
        ListTTree<T>* left;
        ListTTree<T>* right;

        static const TypeInfo* s_typeinfo;

        constexpr ListTNode() : count(0), color(RColor::Black), left(nullptr), right(nullptr) {}
        constexpr ListTNode(size_t cnt, RColor c, ListTTree<T>* l, ListTTree<T>* r) : count(cnt), color(c), left(l), right(r) {}
        constexpr ListTNode(const ListTNode& other) = default;
    };

    template<typename T>
    constexpr TypeInfo g_typeinfo_ListTInlineBuff_generate(uint32_t id, const char* mask, const char* name) {
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
    constexpr TypeInfo g_typeinfo_ListTNode_generate(uint32_t id, const char* name) {
        return {
            id,
            sizeof(ListTNode<T>),
            byteSizeToSlotCount(sizeof(ListTNode<T>)),
            LayoutTag::Ref,
            "0011",
            name,
            nullptr
        };
    }

    template<typename T>
    constexpr TypeInfo g_typeinfo_ListTTree_generate(uint32_t id, const char* mask, const char* name) {
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
        constexpr XList(const ListTInlineBuff<T>& b) : tree(BoxedUnion<ListTTreeUnion<T>>(ListTInlineBuff<T>::s_typeinfo, ListTTreeUnion<T>(b))) {}
        constexpr XList(ListTNode<T>* n) : tree(BoxedUnion<ListTTreeUnion<T>>(ListTNode<T>::s_typeinfo, ListTTreeUnion<T>(n))) {}
        constexpr XList(const ListTTree<T>& t) : tree(t) {}
        constexpr XList(const XList& other) = default;

        template<size_t len>
        constexpr static XList smliteral(const T (&cdata)[len])
        {
            static_assert(len <= LIST_T_CAPACITY(sizeof(T)), "List literal too large for ListTInlineBuff");
            return XList(ListTInlineBuff<T>::literal(cdata));
        }

        constexpr static XList make_empty()
        {
            return XList(ListTInlineBuff<T>::create_empty());
        }

        bool empty() const
        {
            return (this->tree.typeinfo == ListTInlineBuff<T>::s_typeinfo) && this->tree.data.buff.count == 0;
        }

        size_t size() const
        {
            if(this->tree.typeinfo == ListTInlineBuff<T>::s_typeinfo) {
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
}

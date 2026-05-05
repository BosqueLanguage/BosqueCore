#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

#include "postree.h"

namespace ᐸRuntimeᐳ
{
    constexpr static size_t MAX_LIST_INLINE_BYTES = 48; //Bytes -- so 64 total when we add 8 bytes for the size and 8 bytes for the tag or 1 element of the value type if larger!!!

    constexpr size_t LIST_T_CAPACITY(size_t elem_size)
    {
        return std::max(MAX_LIST_INLINE_BYTES / elem_size, (size_t)1);
    }

    template<typename T>
    class ListTInlineContent
    {
    public:
        constexpr static int64_t LIST_T_BUFF_SIZE = LIST_T_CAPACITY(sizeof(T));

        size_t count;
        std::array<T, LIST_T_CAPACITY(sizeof(T))> data;

        constexpr ListTInlineContent() : count(0) { ; }
        constexpr ListTInlineContent(const ListTInlineContent& other) = default;

        constexpr bool empty() const { return this->count == 0; }

        template<size_t len>
        constexpr static ListTInlineContent smliteral(const T (&elems)[len])
        {
            static_assert(len != 0, "ListT inline literal should not be empty");
            static_assert(len <= LIST_T_CAPACITY(sizeof(T)), "Literal too large for ListTInlineContent");

            ListTInlineContent cb;
            std::copy(elems, elems + len, cb.data.begin());
            cb.count = len;

            return cb;
        }

        static ListTInlineContent literaldynamic(const T* elems, size_t len)
        {
            assert(len != 0);
            assert(len <= LIST_T_CAPACITY(sizeof(T)));

            ListTInlineContent cb;
            std::copy(elems, elems + len, cb.data.begin());
            cb.count = len;

            return cb;
        }

        constexpr ListTInlineContent(const T& value): count(1)
        {
            this->data[0] = value;
        }

        ListTInlineContent insert(int64_t index, const T& value) const
        {
            assert(this->count < LIST_T_BUFF_SIZE);
            assert(index < LIST_T_BUFF_SIZE);
           
            ListTInlineContent ninlcnt;
            if(index > 0) {
                std::copy(this->data.cbegin(), this->data.cbegin() + index, ninlcnt.data.begin());
            }
            if(index < (int64_t)this->count) {
                std::copy(this->data.cbegin() + index, this->data.cbegin() + this->count, ninlcnt.data.begin() + index + 1);
            }

            ninlcnt.data[index] = value;
            ninlcnt.count = this->count + 1;

            return ninlcnt;
        }

        constexpr int64_t size() const { return this->count; }
        constexpr T at(size_t index) const { return this->data[index]; }
    };

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    class ListTTreeContent
    {
    public:
        constexpr static int64_t LIST_T_MAX_LEAF_SIZE = ListTInlineContent<T>::LIST_T_BUFF_SIZE * 2;

        PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T> postree;

        static ListTTreeContent mkwpostree(PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T> postree) 
        {
            return ListTTreeContent{ postree };
        } 
        static ListTTreeContent fromInlineList(const ListTInlineContent<T>& inlcnt)
        {
            PosRBTreeLeaf<T, LIST_T_MAX_LEAF_SIZE>* leaf = PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T>::s_leafallocator->allocate(inlcnt.data.cbegin(), inlcnt.data.cend());
            return mkwpostree(PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T>::mkwleaf(leaf));
        }

        static ListTTreeContent smliteral(std::initializer_list<T> elems)
        {
            return ListTTreeContent{PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T>::mkwleaf(PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T>::s_leafallocator->allocate(elems))};
        }

        ListTTreeContent insert(int64_t index, const T& value) const
        {
            return ListTTreeContent{this->postree.insert(index, value)};
        }
    };

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    union ListTUnion
    {
        //empty list is where boxed union typeinfo is nullptr
        ListTInlineContent<T> inlinelist;
        ListTTreeContent<T, TYPE_ID_POS_TREE_T> treelist;

        constexpr ListTUnion() : inlinelist() {}
        constexpr ListTUnion(const ListTUnion& other) = default;

        constexpr ListTUnion(const ListTInlineContent<T>& c) : inlinelist(c) {}
        constexpr ListTUnion(const ListTTreeContent<T, TYPE_ID_POS_TREE_T>& c) : treelist(c) {}
    };

    template<typename T>
    constexpr TypeInfo g_typeinfo_ListTInlineContent_generate(uint32_t id, uint16_t tslots, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(ListTInlineContent<T>),
            byteSizeToSlotCount(sizeof(ListTInlineContent<T>)),
            LayoutTag::ArrayInline,
            tslots,
            mask,
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            name
        };
    }

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    inline constexpr TypeInfo g_typeinfo_ListTTreeContent(uint32_t id, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(ListTTreeContent<T, TYPE_ID_POS_TREE_T>),
            byteSizeToSlotCount(sizeof(ListTTreeContent<T, TYPE_ID_POS_TREE_T>)),
            LayoutTag::Tagged,
            BSQ_TYPEINFO_NO_ESLOT,
            "20",
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            name
        };
    }

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    inline constexpr TypeInfo g_typeinfo_ListT_generate(uint32_t id, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(BoxedUnion<ListTUnion<T, TYPE_ID_POS_TREE_T>>),
            byteSizeToSlotCount(sizeof(BoxedUnion<ListTUnion<T, TYPE_ID_POS_TREE_T>>)),
            LayoutTag::Tagged,
            BSQ_TYPEINFO_NO_ESLOT,
            "200",
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            name
        };
    }

    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    template<typename T, uint32_t TYPE_ID_POS_TREE_T, uint32_t TYPE_ID_INLINE_CONTENT>
    class XListTIterator
    {
    public:
        int64_t index;
        BoxedUnion<ListTUnion<T, TYPE_ID_POS_TREE_T>> ulistt;

        using value_type = T;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(this->ulistt.typeinfo != nullptr);
            
            if(this->ulistt.typeinfo->bsqtypeid == TYPE_ID_INLINE_CONTENT) {
                return this->ulistt.data.inlinelist.at(this->index);
            }
            else {
                return this->ulistt.data.treelist.postree.get(this->index);
            }
        }

        XListTIterator& operator++()
        {
            this->index++;
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

    template<typename T, uint32_t TYPE_ID_LIST_T>
    class XList
    {
    private:
        inline static consteval uint32_t getPosInlineIDFrom(uint32_t treeid) { return treeid - 2; }
        inline static consteval uint32_t getPosTreeIDFrom(uint32_t treeid) { return treeid - 3; }

        BoxedUnion<ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>> ulist;

    public:
        static const TypeInfo* s_inlinetypeinfo;
        static const TypeInfo* s_treetypeinfo;

        constexpr XList() : ulist() {}
        constexpr XList(const ListTInlineContent<T>& b, const TypeInfo* inlinetypeinfo) : ulist(BoxedUnion<ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>>(inlinetypeinfo, ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>(b))) {}
        constexpr XList(const ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>& n, const TypeInfo* treetypeinfo) : ulist(BoxedUnion<ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>>(treetypeinfo, ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>(n))) {}
        constexpr XList(const XList& other) = default;

        XList(const ListTInlineContent<T>& b) : ulist(BoxedUnion<ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>>(s_inlinetypeinfo, ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>(b))) {}
        XList(const ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>& n) : ulist(BoxedUnion<ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>>(s_treetypeinfo, ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>(n))) {}

        template<size_t len>
        constexpr static XList smliteral(const T (&cdata)[len], const TypeInfo* inlinetypeinfo)
        {
            static_assert(len <= LIST_T_CAPACITY(sizeof(T)), "List literal too large for ListTInlineContent");

            return XList(ListTInlineContent<T>::smliteral(cdata), inlinetypeinfo);
        }

        static XList slliteral(std::initializer_list<T> elems, const TypeInfo* treetypeinfo)
        {
            assert(elems.size() != 0);
            assert(elems.size() <= 2 * LIST_T_CAPACITY(sizeof(T)));

            return XList(ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::smliteral(elems), treetypeinfo);
        }

        constexpr static XList make_empty()
        {
            return XList();
        }

        static XList palloc(T* data, size_t count)
        {
            if(count == 0) {
                return XList();
            }
            else {
                if(count <= LIST_T_CAPACITY(sizeof(T))) {
                    ListTInlineContent<T> buff;
                    std::copy(data, data + count, buff.data.begin());
                    buff.count = count;

                    return XList(buff);
                }
                else {
                    assert(false); // Not Implemented: full palloc for CString trees
                }
            }
        }

        bool empty() const
        {
            return this->ulist.typeinfo == nullptr;
        }

        size_t size() const
        {
            if(this->ulist.typeinfo == nullptr) {
                return 0;
            }
            else {
                if(this->ulist.typeinfo == s_inlinetypeinfo) {
                    return this->ulist.data.inlinelist.count;
                }
                else {
                    return this->ulist.data.treelist.postree.count();
                }
            }
        }

        static T gethelper(int64_t index, const XList& list) 
        {
            if(list.ulist.typeinfo == s_inlinetypeinfo) {
                return list.ulist.data.inlinelist.data[index];
            }
            else {
                return list.ulist.data.treelist.postree.get(index);
            }
        }

        T get(int64_t index) const
        {
            return gethelper(index, *this);
        }

        T front() const
        {
            return gethelper(0, *this);
        }

        T back() const
        {
            return gethelper(this->size() - 1, *this);
        }

        XList insert(int64_t index, const T& value) const
        {
            if(this->ulist.typeinfo == nullptr) {
                assert(index == 0);
                return XList(ListTInlineContent<T>(value));
            }
            else {
                if(this->ulist.typeinfo == s_inlinetypeinfo) {
                    if(this->ulist.data.inlinelist.size() < ListTInlineContent<T>::LIST_T_BUFF_SIZE) {
                        return XList(this->ulist.data.inlinelist.insert(index, value));
                    }
                    else {
                        return XList(ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::fromInlineList(this->ulist.data.inlinelist).insert(index, value));
                    }
                }
                else {
                    return XList(this->ulist.data.treelist.insert(index, value));
                }
            }
        }

        XListTIterator<T, getPosTreeIDFrom(TYPE_ID_LIST_T), getPosInlineIDFrom(TYPE_ID_LIST_T)> begin() const
        {
            return XListTIterator<T, getPosTreeIDFrom(TYPE_ID_LIST_T), getPosInlineIDFrom(TYPE_ID_LIST_T)>{0, this->ulist};
        }

        XListTIterator<T, getPosTreeIDFrom(TYPE_ID_LIST_T), getPosInlineIDFrom(TYPE_ID_LIST_T)> end() const
        {
            return XListTIterator<T, getPosTreeIDFrom(TYPE_ID_LIST_T), getPosInlineIDFrom(TYPE_ID_LIST_T)>{(int64_t)this->size(), this->ulist};
        }

        template<bool SafeSimplePred, typename Pred>
        XBool allOf(Pred p) const
        {
            assert(this->ulist.typeinfo != nullptr);

            if(this->ulist.typeinfo == s_inlinetypeinfo) {
                if constexpr (SafeSimplePred) {
                    static_assert(false, "SafeSimplePred is not supported for ListTInlineContent currently");
                }
                else {
                    auto ddend = this->ulist.data.inlinelist.data.cbegin() + this->ulist.data.inlinelist.count;
                    auto ii = std::find_if(this->ulist.data.inlinelist.data.cbegin(), ddend, [p](const T& v) { return !p(v); });
                
                    return XBool::from(ii == ddend);
                }
            }
            else {
                assert(false); // Not Implemented: allOf for ListTTreeContent
            }
        }

        template<bool SafeSimplePred, typename Pred>
        XBool noneOf(Pred p) const
        {
            assert(this->ulist.typeinfo != nullptr);

            if(this->ulist.typeinfo == s_inlinetypeinfo) {
                if constexpr (SafeSimplePred) {
                    static_assert(false, "SafeSimplePred is not supported for ListTInlineContent currently");
                }
                else {
                    auto ddend = this->ulist.data.inlinelist.data.cbegin() + this->ulist.data.inlinelist.count;
                    auto ii = std::find_if(this->ulist.data.inlinelist.data.cbegin(), ddend, [p](const T& v) { return p(v); });
                
                    return XBool::from(ii == ddend);
                }
            }
            else {
                assert(false); // Not Implemented: noneOf for ListTTreeContent
            }
        }

        template<bool SafeSimplePred, typename Pred>
        XBool someOf(Pred p) const
        {
            assert(this->ulist.typeinfo != nullptr);

            if(this->ulist.typeinfo == s_inlinetypeinfo) {
                if constexpr (SafeSimplePred) {
                    static_assert(false, "SafeSimplePred is not supported for ListTInlineContent currently");
                }
                else {
                    auto ddend = this->ulist.data.inlinelist.data.cbegin() + this->ulist.data.inlinelist.count;
                    auto ii = std::find_if(this->ulist.data.inlinelist.data.cbegin(), ddend, [p](const T& v) { return p(v); });
                
                    return XBool::from(ii != ddend);
                }
            }
            else {
                assert(false); // Not Implemented: someOf for ListTTreeContent
            }
        }
    };
}
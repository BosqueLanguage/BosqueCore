#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "postree.h"

namespace ᐸRuntimeᐳ
{
    constexpr static size_t MAX_LIST_INLINE_BYTES = 32; //Bytes -- so 40 total when we add 8 bytes for the size

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
        std::array<T, LIST_T_BUFF_SIZE> data;

        constexpr ListTInlineContent() : count{0}, data{} { ; } 
        constexpr ListTInlineContent(const ListTInlineContent& other) = default;

        constexpr bool empty() const { return this->count == 0; }

        constexpr ListTInlineContent(const T& value): count(1), data{value} { ; }

        constexpr static void zerofill(std::array<T, LIST_T_BUFF_SIZE>& data, size_t ecount)
        {
            std::fill(data.begin() + ecount, data.end(), T{});
        }

        template<size_t len>
        constexpr ListTInlineContent(const T (&elems)[len]) : count{len}
        {
            static_assert(len != 0, "ListT inline literal should not be empty");
            static_assert(len <= LIST_T_BUFF_SIZE, "Literal too large for ListTInlineContent");

            std::copy(elems, elems + len, this->data.begin());

            if constexpr (len < LIST_T_BUFF_SIZE) {
                zerofill(this->data, len);
            }
        }

        ListTInlineContent(const T* elems, size_t len) : count{len}
        {
            assert(len != 0);
            assert(len <= LIST_T_BUFF_SIZE);

            std::copy(elems, elems + len, this->data.begin());

            if(len < LIST_T_BUFF_SIZE) {
                zerofill(this->data, len);
            }
        }

        /** Constructor when we have a range of values  **/
        template<typename Iter>
        ListTInlineContent(Iter start, Iter end)
        {            
            const size_t size = std::distance(start, end);
            assert(size != 0);
            assert(size <= LIST_T_BUFF_SIZE);

            std::copy(start, end, this->data.begin());
            this->count = size; 
            
            if(size < LIST_T_BUFF_SIZE) {
                zerofill(this->data, size);
            }
        }

        /** Push the element at the front of the list **/
        ListTInlineContent(const T& value, const ListTInlineContent& src) : count{src.count + 1}
        {
            assert(src.count < LIST_T_BUFF_SIZE);

            this->data[0] = value;
            std::copy(src.data.cbegin(), src.data.cbegin() + src.count, this->data.begin() + 1);

            if(this->count < LIST_T_BUFF_SIZE) {
                zerofill(this->data, this->count);
            }
        }

        /** Push the element at the end of the list **/
        ListTInlineContent(const ListTInlineContent& src, const T& value) : count{src.count + 1}
        {
            assert(src.count < LIST_T_BUFF_SIZE);

            std::copy(src.data.cbegin(), src.data.cbegin() + src.count, this->data.begin());
            this->data[src.count] = value;

            if(this->count < LIST_T_BUFF_SIZE) {
                zerofill(this->data, this->count);
            }
        }

        /** Push the element in the middle of the list **/
        ListTInlineContent(const ListTInlineContent& src, int64_t index, const T& value) : count{src.count + 1}
        {
            assert(src.count < LIST_T_BUFF_SIZE);
            assert(index < LIST_T_BUFF_SIZE);
           
            std::copy(src.data.cbegin(), src.data.cbegin() + index, this->data.begin());
            this->data[index] = value;
            std::copy(src.data.cbegin() + index, src.data.cbegin() + src.count, this->data.begin() + index + 1);
            
            if(this->count < LIST_T_BUFF_SIZE) {
                zerofill(this->data, this->count);
            }
        }

        constexpr int64_t size() const { return this->count; }

        constexpr T getFront() const { return this->data[0]; }
        constexpr T getBack() const { return this->data[this->count - 1]; }
        constexpr T at(size_t index) const { return this->data[index]; }
    };

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    class ListTTreeContent
    {
    public:
        constexpr static int64_t LIST_T_MAX_LEAF_SIZE = std::max(ListTInlineContent<T>::LIST_T_BUFF_SIZE * 2, (size_t)4);

        size_t tag;
        PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T> postree;

        ListTTreeContent() : tag{std::numeric_limits<size_t>::max()}, postree{} { ; }
        ListTTreeContent(const ListTTreeContent& other) = default;
        ListTTreeContent(const PosRBTree<T, LIST_T_MAX_LEAF_SIZE, TYPE_ID_POS_TREE_T>& postree) : tag{std::numeric_limits<size_t>::max()}, postree{postree} { ; }
    };

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    union ListTUnion
    {
        //empty list is inlinelist
        ListTInlineContent<T> inlinelist;
        ListTTreeContent<T, TYPE_ID_POS_TREE_T> treelist;

        constexpr ListTUnion() : inlinelist() {}
        constexpr ListTUnion(const ListTUnion& other) = default;

        constexpr ListTUnion(const ListTInlineContent<T>& c) : inlinelist{c} {}
        constexpr ListTUnion(const ListTTreeContent<T, TYPE_ID_POS_TREE_T>& c) : treelist{c} {}

        constexpr bool empty() const { return this->inlinelist.empty(); }

        constexpr bool isInline() const { return this->inlinelist.size() < std::numeric_limits<size_t>::max(); }
        constexpr bool isTree() const { return this->inlinelist.size() == std::numeric_limits<size_t>::max(); }
    };

    template<typename T>
    constexpr TypeInfo g_typeinfo_ListTInlineContent_generate(uint32_t id, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(ListTInlineContent<T>),
            byteSizeToSlotCount(sizeof(ListTInlineContent<T>)),
            LayoutTag::Value,
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
            LayoutTag::Value,
            "01",
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
            sizeof(ListTUnion<T, TYPE_ID_POS_TREE_T>),
            byteSizeToSlotCount(sizeof(ListTUnion<T, TYPE_ID_POS_TREE_T>)),
            LayoutTag::Value,
            "40",
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
        ListTUnion<T, TYPE_ID_POS_TREE_T> ulistt;

        using value_type = T;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(this->ulistt.typeinfo != nullptr);
            
            if(this->ulistt.isInline()) {
                return this->ulistt.inlinelist.at(this->index);
            }
            else {
                return this->ulistt.treelist.postree.get(this->index);
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
        constexpr XList(const XList& other) = default;
        constexpr XList(const ListTInlineContent<T>& b) : ulist{b} { ; }
        constexpr XList(const ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>& n) : ulist{n} { ; }

        template<size_t len>
        constexpr XList(const T (&elems)[len]) : ulist{ListTInlineContent<T>(elems, len)} { ; }
        {
            static_assert(0 <= len);
            static_assert(len <= ListTInlineContent<T>::LIST_T_BUFF_SIZE);
        }

        static XList mk(std::initializer_list<T> elems)
        {
            if(elems.size() == 0) {
                return XList();
            }
            else {
                if(elems.size() <= ListTInlineContent<T>::LIST_T_BUFF_SIZE) {
                    return XList(ListTInlineContent<T>(elems.begin(), elems.end()));
                }
                else if(elems.size() <= ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::LIST_T_MAX_LEAF_SIZE) {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::LIST_T_MAX_LEAF_SIZE, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(elems.begin(), elems.end())}};
                }
                else {
                    assert(false); // Not Implemented: full mk for CString trees
                }
            }
        }

        constexpr bool empty() const
        {
            return this->ulist.empty();
        }

        size_t size() const
        {
            if(this->ulist.empty()) {
                return 0;
            }
            else {
                if(this->ulist.isInline()) {
                    return this->ulist.inlinelist.size();
                }
                else {
                    return this->ulist.treelist.postree.count();
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

        T getFront() const
        {
            if(this->ulist.isInline()) {
                return this->ulist.inlinelist.getFront();
            }
            else {
                return this->ulist.treelist.postree.getFront();
            }
        }

        T getBack() const
        {
            if(this->ulist.isInline()) {
                return this->ulist.inlinelist.getBack();
            }
            else {
                return this->ulist.treelist.postree.getBack();
            }
        }

        T get(int64_t index) const
        {
            if(this->ulist.isInline()) {
                return this->ulist.inlinelist.at(index);
            }
            else {
                return this->ulist.treelist.postree.get(index);
            }
        }

        XList pushBack(const T& value) const
        {
            if(this->ulist.empty()) {
                return XList{ListTInlineContent<T>{value}};
            }
            else {
                if(this->ulist.isInline()) {
                    if(this->ulist.inlinelist.size() < ListTInlineContent<T>::LIST_T_BUFF_SIZE) {
                        return XList{this->ulist.inlinelist.pushBack(value)};
                    }
                    else {
                        return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::LIST_T_MAX_LEAF_SIZE, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count, value)}};
                    }
                }
                else {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{this->ulist.treelist.pushBack(value)}};
                }
            }
        }

        XList pushFront(const T& value) const
        {
            if(this->ulist.empty()) {
                return XList{ListTInlineContent<T>{value}};
            }
            else {
                if(this->ulist.isInline()) {
                    if(this->ulist.inlinelist.size() < ListTInlineContent<T>::LIST_T_BUFF_SIZE) {
                        return XList{this->ulist.inlinelist.pushFront(value)};
                    }
                    else {
                        return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::LIST_T_MAX_LEAF_SIZE, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(value, this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count)}};
                    }
                }
                else {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{this->ulist.treelist.pushFront(value)}};
                }
            }
        }

        XList insert(int64_t index, const T& value) const
        {
            if(this->ulist.empty()) {
                assert(index == 0);
                return XList{ListTInlineContent<T>{value}};
            }
            else {
                if(this->ulist.isInline()) {
                    if(this->ulist.inlinelist.size() < ListTInlineContent<T>::LIST_T_BUFF_SIZE) {
                        return XList{this->ulist.inlinelist.insert(index, value)};
                    }
                    else {
                        return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::LIST_T_MAX_LEAF_SIZE, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + index, value, this->ulist.inlinelist.data.begin() + index, this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count)}};
                    }
                }
                else {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{this->ulist.treelist.insert(index, value)}};
                }
            }
        }
/*
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
*/
    };
}

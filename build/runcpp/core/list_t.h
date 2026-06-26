#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "postree.h"

namespace ᐸRuntimeᐳ
{
    constexpr static size_t MAX_LIST_INLINE_BYTES = 32; //Bytes -- so 40 total when we add 8 bytes for the size
    
    constexpr size_t LIST_T_INLINE_CAPACITY(size_t elem_size)
    {
         //at least 1 element but up to the number that can fit in the max inline bytes
        return std::max(MAX_LIST_INLINE_BYTES / elem_size, (size_t)1);
    }

    constexpr size_t LIST_T_LEAF_CAPACITY(size_t elem_size)
    {
        //leaf should be big enough to hold a map(..) operation result from any type AND also be larger than the inline capacity (which-ever is larger)
        return (MAX_LIST_INLINE_BYTES / 8) + 1;
    }

    constexpr auto fn_lambdaand = [](XBool a, XBool b) { return a & b; };
    constexpr auto fn_lambdaor = [](XBool a, XBool b) { return a | b; };

    template<typename T>
    class ListTInlineContent
    {
    public:
        constexpr static int64_t MAX_INLINE_CAPACITY = LIST_T_INLINE_CAPACITY(sizeof(T));
        constexpr static std::array<XNat, MAX_INLINE_CAPACITY> idx_range = create_idx_range<MAX_INLINE_CAPACITY>();

        size_t count;
        std::array<T, MAX_INLINE_CAPACITY> data;

#ifdef BSQ_POSTREE_VALIDATE
        void toValues(std::vector<T>& result) const
        {
            for(size_t i = 0; i < this->count; i++) {
                result.push_back(this->data[i]);
            }
        }

        template <typename Fn>
        std::string toJSON(Fn pf) const
        {
            std::string result = "{count: " + std::to_string(this->count) + ", data: [";
            for(size_t i = 0; i < this->count; i++) {
                result += pf(this->data[i]);
                if(i != this->count - 1) {
                    result += ", ";
                }
            }
            result += "]}";
            return result;
        }
#endif

        constexpr ListTInlineContent() : count{0}, data{} { ; } 
        constexpr ListTInlineContent(const ListTInlineContent& other) = default;

        constexpr bool empty() const { return this->count == 0; }

        constexpr ListTInlineContent(const T& value): count(1), data{value} { ; }

        constexpr static void zerofill(std::array<T, MAX_INLINE_CAPACITY>& data, size_t ecount)
        {
            std::fill(data.begin() + ecount, data.end(), T{});
        }

        template<size_t len>
        constexpr ListTInlineContent(const T (&elems)[len]) : count{len}
        {
            static_assert(len != 0, "ListT inline literal should not be empty");
            static_assert(len <= MAX_INLINE_CAPACITY, "Literal too large for ListTInlineContent");

            std::copy(elems, elems + len, this->data.begin());

            if constexpr (len < MAX_INLINE_CAPACITY) {
                zerofill(this->data, len);
            }
        }

        ListTInlineContent(const T* elems, size_t len) : count{len}
        {
            assert(len != 0);
            assert(len <= MAX_INLINE_CAPACITY);

            std::copy(elems, elems + len, this->data.begin());

            if(len < MAX_INLINE_CAPACITY) {
                zerofill(this->data, len);
            }
        }

        /** Constructor when we have a range of values  **/
        template<typename Iter>
        ListTInlineContent(Iter start, Iter end)
        {            
            const size_t size = std::distance(start, end);
            assert(size != 0);
            assert(size <= MAX_INLINE_CAPACITY);

            std::copy(start, end, this->data.begin());
            this->count = size; 
            
            if(size < MAX_INLINE_CAPACITY) {
                zerofill(this->data, size);
            }
        }

        /** Push the element at the front of the list **/
        ListTInlineContent(const T& value, const ListTInlineContent& src) : count{src.count + 1}
        {
            assert(src.count < MAX_INLINE_CAPACITY);

            this->data[0] = value;
            std::copy(src.data.cbegin(), src.data.cbegin() + src.count, this->data.begin() + 1);

            if(this->count < MAX_INLINE_CAPACITY) {
                zerofill(this->data, this->count);
            }
        }

        /** Push the element at the end of the list **/
        ListTInlineContent(const ListTInlineContent& src, const T& value) : count{src.count + 1}
        {
            assert(src.count < MAX_INLINE_CAPACITY);

            std::copy(src.data.cbegin(), src.data.cbegin() + src.count, this->data.begin());
            this->data[src.count] = value;

            if(this->count < MAX_INLINE_CAPACITY) {
                zerofill(this->data, this->count);
            }
        }

        /** Constructor for middle replacement **/
        template<typename Iter>
        ListTInlineContent(Iter lstart, Iter lend, const T& value, Iter rstart, Iter rend)
        {   
            const size_t size = std::distance(lstart, lend) + 1 + std::distance(rstart, rend);
            assert(size != 0);
            assert(size <= MAX_INLINE_CAPACITY);

            std::copy(lstart, lend, this->data.begin());
            this->data[std::distance(lstart, lend)] = value;
            std::copy(rstart, rend, this->data.begin() + std::distance(lstart, lend) + 1);
            this->count = size;

            if(size < MAX_INLINE_CAPACITY) {
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
        constexpr static int64_t MAX_LEAF_CAPACITY = LIST_T_LEAF_CAPACITY(sizeof(T));

        size_t tag;
        PosRBTree<T, MAX_LEAF_CAPACITY, TYPE_ID_POS_TREE_T> postree;

        ListTTreeContent() : tag{std::numeric_limits<size_t>::max()}, postree{} { ; }
        ListTTreeContent(const ListTTreeContent& other) = default;
        ListTTreeContent(const PosRBTree<T, MAX_LEAF_CAPACITY, TYPE_ID_POS_TREE_T>& postree) : tag{std::numeric_limits<size_t>::max()}, postree{postree} { ; }
    };

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    union ListTUnion
    {
        static_assert(sizeof(ListTInlineContent<T>) >= sizeof(ListTTreeContent<T, TYPE_ID_POS_TREE_T>));

        //empty list is inlinelist, upunning type type punning for assignment and default initialization
        std::array<uint8_t, sizeof(ListTInlineContent<T>)> upunning;
        ListTInlineContent<T> inlinelist;
        ListTTreeContent<T, TYPE_ID_POS_TREE_T> treelist;

        constexpr ListTUnion() : upunning{} { ; }
        constexpr ListTUnion(const ListTUnion& other) = default;

        constexpr ListTUnion(const ListTInlineContent<T>& c) : inlinelist{c} { ; }
        constexpr ListTUnion(const ListTTreeContent<T, TYPE_ID_POS_TREE_T>& c) : treelist{c} { ; }

        constexpr bool empty() const { return this->inlinelist.empty(); }

        constexpr bool isInline() const { return this->inlinelist.count < std::numeric_limits<size_t>::max(); }
        constexpr bool isTree() const { return this->inlinelist.count == std::numeric_limits<size_t>::max(); }


        constexpr ListTUnion& operator=(const ListTUnion& other)
        {
            if(this == &other) {
                return *this;
            }

            this->upunning = other.upunning;
            return *this;
        }
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
            name,
            false
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
            name,
            false
        };
    }

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    inline constexpr TypeInfo g_typeinfo_ListT_generate(uint32_t id, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(ListTUnion<T, TYPE_ID_POS_TREE_T>),
            byteSizeToSlotCount(sizeof(ListTUnion<T, TYPE_ID_POS_TREE_T>)),
            LayoutTag::Value,
            mask,
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            name,
            false
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
            assert(!this->ulistt.empty());
            
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

        ListTUnion<T, getPosTreeIDFrom(TYPE_ID_LIST_T)> ulist;

    public:
        constexpr XList() : ulist{} {}
        constexpr XList(const XList& other) = default;
        constexpr XList(const ListTInlineContent<T>& b) : ulist{b} { ; }
        constexpr XList(const ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>& n) : ulist{n} { ; }

        template<size_t len>
        constexpr XList(const T (&elems)[len]) : ulist{ListTInlineContent<T>(elems, len)} { ; }

        static XList mk(std::initializer_list<T> elems)
        {
            if(elems.size() == 0) {
                return XList{};
            }
            else {
                if(elems.size() <= ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                    return XList(ListTInlineContent<T>(elems.begin(), elems.end()));
                }
                else if(elems.size() <= ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY) {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(elems.begin(), elems.end())}};
                }
                else {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mklargerec(elems.begin(), elems.end(), elems.size())}};
                }
            }
        }

        static XList mk(const T* elems, size_t len)
        {
            if(len == 0) {
                return XList{};
            }
            else {
                if(len <= ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                    return XList(ListTInlineContent<T>(elems, elems + len));
                }
                else if(len <= ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY) {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(elems, elems + len)}};
                }
                else {
                    return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mklargerec(elems, elems + len, len)}};
                }
            }
        }

#ifdef BSQ_POSTREE_VALIDATE
        template <typename Fn>
        std::string toString(Fn pf) const
        {
            if(this->ulist.empty()) {
                return "[]";
            }
            else {
                std::vector<T> values;
                if(this->ulist.isInline()) {
                    this->ulist.inlinelist.toValues(values);
                }
                else {
                    this->ulist.treelist.postree.toValues(values);
                }

                std::string result = "[";
                for(size_t i = 0; i < values.size(); i++) {
                    result += pf(values[i]);
                    if(i != values.size() - 1) {
                        result += ", ";
                    }
                }
                result += "]";
                return result;
            }
        }

        template <typename Fn>
        std::string toJSON(Fn pf) const
        {
            if(this->ulist.empty()) {
                return "null";
            }
            else {
                if(this->ulist.isInline()) {
                    return this->ulist.inlinelist.toJSON(pf);
                }
                else {
                    return this->ulist.treelist.postree.toJSON(pf);
                }
            }
        }
#endif

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
                    return this->ulist.treelist.postree.size();
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
                    if(this->ulist.inlinelist.size() < ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                        return XList{ListTInlineContent<T>{this->ulist.inlinelist, value}};
                    }
                    else {
                        return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count, value)}};
                    }
                }
                else {
                    return XList{this->ulist.treelist.postree.pushBack(value)};
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
                    if(this->ulist.inlinelist.size() < ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                        return XList{ListTInlineContent<T>{value, this->ulist.inlinelist}};
                    }
                    else {
                        return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(value, this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count)}};
                    }
                }
                else {
                    return XList{this->ulist.treelist.postree.pushFront(value)};
                }
            }
        }

        XList set(int64_t index, const T& value) const
        {
            if(this->ulist.isInline()) {
                return XList{ListTInlineContent<T>{this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + index, value, this->ulist.inlinelist.data.begin() + index + 1, this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count}};
            }
            else {
                return XList{this->ulist.treelist.postree.set(index, value)};
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
                    if(this->ulist.inlinelist.size() < ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                        return XList{ListTInlineContent<T>{this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + index, value, this->ulist.inlinelist.data.begin() + index, this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count}};
                    }
                    else {
                        return XList{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(this->ulist.inlinelist.data.begin(), this->ulist.inlinelist.data.begin() + index, value, this->ulist.inlinelist.data.begin() + index, this->ulist.inlinelist.data.begin() + this->ulist.inlinelist.count)}};
                    }
                }
                else {
                    return XList{this->ulist.treelist.postree.insert(index, value)};
                }
            }
        }

        template<bool SafeSimplePred, typename Pred>
        XBool allOf(Pred p) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                if constexpr (SafeSimplePred) {
                    return XBool::from(std::all_of(std::execution::unseq, ddbegin, ddend, p));
                }
                else {
                    auto ii = std::find_if_not(ddbegin, ddend, p);
                    return XBool::from(ii == ddend);
                }
            }
            else {
                return this->ulist.treelist.postree.template allof<SafeSimplePred, Pred>(p);
            }
        }

        template<bool SafeSimplePred, typename Pred>
        XBool noneOf(Pred p) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                if constexpr (SafeSimplePred) {
                    return XBool::from(std::none_of(std::execution::unseq, ddbegin, ddend, p));
                }
                else {
                    auto ii = std::find_if(ddbegin, ddend, p);
                    return XBool::from(ii == ddend);
                }
            }
            else {
                return this->ulist.treelist.postree.template noneof<SafeSimplePred, Pred>(p);
            }
        }

        template<bool SafeSimplePred, typename Pred>
        XBool someOf(Pred p) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                if constexpr (SafeSimplePred) {
                    return XBool::from(std::any_of(std::execution::unseq, ddbegin, ddend, p));
                }
                else {
                    auto ii = std::find_if(ddbegin, ddend, p);
                    return XBool::from(ii != ddend);
                }
            }
            else {
                return this->ulist.treelist.postree.template someof<SafeSimplePred, Pred>(p);
            }
        }

        template<bool SafeSimpleFn, typename U, uint32_t TYPE_ID_LIST_U, typename Fn>
        XList<U, TYPE_ID_LIST_U> map(Fn f) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY> result{};
                std::transform(ddbegin, ddend, result.begin(), f);
                
                if(this->ulist.inlinelist.count <= ListTInlineContent<U>::MAX_INLINE_CAPACITY) {
                    return XList<U, TYPE_ID_LIST_U>{ListTInlineContent<U>(result.data(), this->ulist.inlinelist.count)};
                }
                else {
                    return XList<U, TYPE_ID_LIST_U>{ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>{PosRBTree<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_U)>::mkinitial(result.data(), result.data() + this->ulist.inlinelist.count)}};
                }
            }
            else {
                return XList<U, TYPE_ID_LIST_U>{ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>{this->ulist.treelist.postree.template map<SafeSimpleFn, U, getPosTreeIDFrom(TYPE_ID_LIST_U), Fn>(f)}};
            }
        }

        template<bool SafeSimpleFn, typename U, uint32_t TYPE_ID_LIST_U, typename Fn>
        XList<U, TYPE_ID_LIST_U> mapIdx(Fn f) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                constexpr std::array<XNat, ListTInlineContent<T>::MAX_INLINE_CAPACITY> zipidx = create_idx_range<ListTInlineContent<T>::MAX_INLINE_CAPACITY>();

                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY> result{};
                std::transform(ddbegin, ddend, zipidx.begin(), result.begin(), f);
                
                if(this->ulist.inlinelist.count <= ListTInlineContent<U>::MAX_INLINE_CAPACITY) {
                    return XList<U, TYPE_ID_LIST_U>{ListTInlineContent<U>(result.data(), this->ulist.inlinelist.count)};
                }
                else {
                    return XList<U, TYPE_ID_LIST_U>{ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>{PosRBTree<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_U)>::mkinitial(result.data(), result.data() + this->ulist.inlinelist.count)}};
                }
            }
            else {
                return XList<U, TYPE_ID_LIST_U>{ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>{this->ulist.treelist.postree.template mapIdx<SafeSimpleFn, U, getPosTreeIDFrom(TYPE_ID_LIST_U), Fn>(f)}};
            }
        }

        template<bool SafeSimpleFn, typename Pred>
        XList<T, TYPE_ID_LIST_T> filter(Pred p) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY> result{};
                auto eiter = std::copy_if(ddbegin, ddend, result.begin(), p);
                
                if(eiter == result.begin()) {
                    return XList<T, TYPE_ID_LIST_T>{};
                }
                else {
                    return XList<T, TYPE_ID_LIST_T>{ListTInlineContent<T>(result.data(), std::distance(result.begin(), eiter))};
                }
            }
            else {
                PosRBData<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY> dres;
                PosRBNode<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY>* opttree = this->ulist.treelist.postree.template filter<SafeSimpleFn, Pred>(dres, p);
                if(opttree == nullptr) {
                    if(dres.dcount == 0) {
                        return XList<T, TYPE_ID_LIST_T>{};
                    }
                    else if(dres.dcount <= ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                        return XList<T, TYPE_ID_LIST_T>{ListTInlineContent<T>(dres.data.data(), dres.dcount)};
                    }
                    else {
                        return XList<T, TYPE_ID_LIST_T>{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(dres.data.data(), dres.data.data() + dres.dcount)}};
                    }
                }
                else {
                    return XList<T, TYPE_ID_LIST_T>{ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>{opttree}};
                }
            }
        }

        template<bool BothSafeSimpleFn, typename U, uint32_t TYPE_ID_LIST_U, typename Pred, typename Fn>
        XList<U, TYPE_ID_LIST_U> filtermap(Pred p, Fn f) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<T, ListTTreeContent<T, getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY> fresult{};
                auto feiter = std::copy_if(ddbegin, ddend, fresult.begin(), p);

                if(feiter == fresult.begin()) {
                    return XList<U, TYPE_ID_LIST_U>{};
                }
                else {
                    std::array<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY> mresult{};
                    auto meiter = std::transform(fresult.begin(), feiter, mresult.begin(), f);
                    
                    if(std::distance(mresult.begin(), meiter) < ListTInlineContent<U>::MAX_INLINE_CAPACITY) {
                        return XList<U, TYPE_ID_LIST_U>{ListTInlineContent<U>(mresult.data(), std::distance(mresult.begin(), meiter))};
                    }
                    else {
                        return XList<U, TYPE_ID_LIST_U>{ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>{PosRBTree<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_U)>::mkinitial(mresult.data(), mresult.data() + std::distance(mresult.begin(), meiter))}};
                    }
                }
            }
            else {
                PosRBData<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY> dres;
                PosRBNode<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY>* opttree = this->ulist.treelist.postree.template filtermap<BothSafeSimpleFn, U, TYPE_ID_LIST_U, Pred, Fn>(dres, p, f);
                if(opttree == nullptr) {
                    if(dres.dcount == 0) {
                        return XList<U, TYPE_ID_LIST_U>{};
                    }
                    else if(dres.dcount <= ListTInlineContent<U>::MAX_INLINE_CAPACITY) {
                        return XList<U, TYPE_ID_LIST_U>{ListTInlineContent<U>(dres.data.data(), dres.dcount)};
                    }
                    else {
                        return XList<U, TYPE_ID_LIST_U>{ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>{PosRBTree<U, ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>::MAX_LEAF_CAPACITY, getPosTreeIDFrom(TYPE_ID_LIST_U)>::mkinitial(dres.data.data(), dres.data.data() + dres.dcount)}};
                    }
                }
                else {
                    return XList<U, TYPE_ID_LIST_U>{ListTTreeContent<U, getPosTreeIDFrom(TYPE_ID_LIST_U)>{opttree}};
                }
            }
        }

        template<bool SafeSimpleFn, typename Pred>
        T minfun(Pred p) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                if constexpr (SafeSimpleFn) {
                    return *std::min_element(std::execution::unseq, ddbegin, ddend, p);
                }
                else {
                    return *std::min_element<std::execution::seq>(ddbegin, ddend, p);
                }
            }
            else {
                return this->ulist.treelist.postree.template minfun<SafeSimpleFn>(p);
            }
        }

        T sum(T zero) const
        {
            if(this->ulist.empty()) {
                return zero;
            }

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                return std::accumulate(ddbegin, ddend, zero, [](T a, T b) {
                    T::checkOverflowAddition(a, b, "List Sum", 0);
                    return a + b;
                });
            }
            else {
                return this->ulist.treelist.postree.sum(zero);
            }
        }

        template<bool SafeSimpleFn, typename Fn>
        T sumfun(T zero, Fn op) const
        {
            if(this->ulist.empty()) {
                return zero;
            }

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                return std::accumulate(ddbegin, ddend, zero, [&op](const T& a, const T& b) {
                    return op(a, b);
                });
            }
            else {
                return this->ulist.treelist.postree.template sumfun<SafeSimpleFn>(zero, op);
            }
        }

        template <typename Fn>
        void diagnosticEmit(std::ostream& out, const TypeInfo* ltype, Fn diagnosticEmitFn, bool waddr) const
        {
            if(this->ulist.isInline()) {
                out << ltype->typekey;
                out << '{';
                for(size_t i = 0; i < this->ulist.inlinelist.count; i++) {
                    if(i != 0) {
                        out << ", ";
                    }
                    diagnosticEmitFn(out, this->ulist.inlinelist.data[i], waddr);
                }
                out << '}';
            }
            else {
                this->ulist.treelist.postree.diagnosticEmit(out, ltype, diagnosticEmitFn, waddr);
            }
        }
    };

    namespace XListOps 
    {
        template <typename T, uint32_t TYPE_ID_LIST_T>
        XList<T, TYPE_ID_LIST_T> fromRange(int64_t start, int64_t end)
        {
            if(end - start <= ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                std::array<T, ListTInlineContent<T>::MAX_INLINE_CAPACITY> result{};
                for(int64_t i = 0; i < end - start; i++) {
                    result[i] = T{start + i};
                }

                return XList<T, TYPE_ID_LIST_T>{ListTInlineContent<T>(result.data(), end - start)};
            }
            else if(end - start <= ListTTreeContent<T, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY) {
                std::array<T, ListTTreeContent<T, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY> result{};
                for(int64_t i = 0; i < end - start; i++) {
                    result[i] = T{start + i};
                }

                return XList<T, TYPE_ID_LIST_T>{ListTTreeContent<T, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkinitial(result.data(), result.data() + (end - start))}};
            }
            else {
                return XList<T, TYPE_ID_LIST_T>{ListTTreeContent<T, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>{PosRBTree<T, ListTTreeContent<T, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>::MAX_LEAF_CAPACITY, XList<T, TYPE_ID_LIST_T>::getPosTreeIDFrom(TYPE_ID_LIST_T)>::mkrange(start, end)}};
            }
        }

        template <typename J, uint32_t TYPE_ID_LIST_J, typename ListT, typename ListU>
        XList<J, TYPE_ID_LIST_J> zip(const ListT& l1, const ListU& l2, int64_t ssize)
        {
            if(ssize < ListTInlineContent<J>::MAX_INLINE_CAPACITY) {
                std::array<J, ListTInlineContent<J>::MAX_INLINE_CAPACITY> result{};
                for(int64_t i = 0; i < ssize; i++) {
                    result[i] = J{l1.get(i), l2.get(i)};
                }

                return XList<J, TYPE_ID_LIST_J>{ListTInlineContent<J>(result.data(), ssize)};
            }
            else if(ssize < ListTTreeContent<J, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>::MAX_LEAF_CAPACITY) {
                std::array<J, ListTTreeContent<J, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>::MAX_LEAF_CAPACITY> result{};
                for(int64_t i = 0; i < ssize; i++) {
                    result[i] = J{l1.get(i), l2.get(i)};
                }

                return XList<J, TYPE_ID_LIST_J>{ListTTreeContent<J, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>{PosRBTree<J, ListTTreeContent<J, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>::MAX_LEAF_CAPACITY, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>::mkinitial(result.data(), result.data() + ssize)}};
            }
            else {
                return XList<J, TYPE_ID_LIST_J>{ListTTreeContent<J, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>{PosRBTree<J, ListTTreeContent<J, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>::MAX_LEAF_CAPACITY, XList<J, TYPE_ID_LIST_J>::getPosTreeIDFrom(TYPE_ID_LIST_J)>::mkzip(l1.begin(), l2.begin(), ssize)}};
            }
        }
    }

    constexpr bool gcIsListTInline(void** ptr) { return *((size_t*)ptr) < std::numeric_limits<size_t>::max(); }
}

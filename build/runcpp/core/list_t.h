#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "postree.h"

namespace ᐸRuntimeᐳ
{
    constexpr static size_t MAX_LIST_INLINE_BYTES = 32; //Bytes -- so 40 total when we add 8 bytes for the size
    
    consteval size_t LIST_T_INLINE_CAPACITY(size_t elem_size)
    {
         //at least 1 element but up to the number that can fit in the max inline bytes
        return std::max(MAX_LIST_INLINE_BYTES / elem_size, (size_t)1);
    }

    consteval size_t LIST_T_LEAF_CAPACITY(size_t elem_size)
    {
        //leaf should be big enough to hold a map(..) operation result from any type AND also be larger than the inline capacity (which-ever is larger)
        return (MAX_LIST_INLINE_BYTES / 8) + 1;
    }

    struct LambdaAndFn
    {
        XBool operator()(XBool a, XBool b) const 
        { 
            return a & b; 
        }
    };

    struct LambdaOrFn
    {
        XBool operator()(XBool a, XBool b) const 
        { 
            return a | b; 
        }
    };

    template<typename T>
    class ListTInlineContent
    {
    public:
        constexpr static int64_t MAX_INLINE_CAPACITY = LIST_T_INLINE_CAPACITY(sizeof(T));
        constexpr static std::array<XNat, MAX_INLINE_CAPACITY> idx_range = create_idx_range<MAX_INLINE_CAPACITY>();

        size_t count;
        std::array<T, MAX_INLINE_CAPACITY> data;

        void toValues(std::vector<T>& result) const
        {
            for(size_t i = 0; i < this->count; i++) {
                result.push_back(this->data[i]);
            }
        }

        ListTInlineContent() : count{0}, data{} { ; } 
        ListTInlineContent(const ListTInlineContent& other) = default;

        bool empty() const { return this->count == 0; }

        ListTInlineContent(const T& value): count(1), data{value} { ; }

        static void zerofill(std::array<T, MAX_INLINE_CAPACITY>& data, size_t ecount)
        {
            std::fill(data.begin() + ecount, data.end(), T{});
        }

        template<size_t len>
        ListTInlineContent(const T (&elems)[len]) : count{len}
        {
            static_assert(len != 0, "ListT inline literal should not be empty");
            static_assert(len <= MAX_INLINE_CAPACITY, "Literal too large for ListTInlineContent");

            std::copy(elems, elems + len, this->data.begin());

            if(len < MAX_INLINE_CAPACITY) {
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

        /** Constructor for append **/
        template<typename Iter>
        ListTInlineContent(Iter lstart, Iter lend, Iter rstart, Iter rend)
        {   
            const size_t size = std::distance(lstart, lend) + std::distance(rstart, rend);
            assert(size != 0);
            assert(size <= MAX_INLINE_CAPACITY);

            std::copy(lstart, lend, this->data.begin());
            std::copy(rstart, rend, this->data.begin() + std::distance(lstart, lend));
            this->count = size;

            if(size < MAX_INLINE_CAPACITY) {
                zerofill(this->data, this->count);
            }
        }

        int64_t size() const { return this->count; }

        T getFront() const { return this->data[0]; }
        T getBack() const { return this->data[this->count - 1]; }
        T at(size_t index) const { return this->data[index]; }
    };

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    class ListTTreeContent
    {
    public:
        constexpr static int64_t MAX_LEAF_CAPACITY = LIST_T_LEAF_CAPACITY(sizeof(T));
        constexpr static size_t GC_SKIP_SLOTS = std::numeric_limits<uint32_t>::max() + (ListTInlineContent<T>::MAX_INLINE_CAPACITY * sizeof(T) / sizeof(void*));

        size_t tag;
        PosRBTree<T, MAX_LEAF_CAPACITY, TYPE_ID_POS_TREE_T> postree;

        ListTTreeContent() : tag{GC_SKIP_SLOTS}, postree{} { ; }
        ListTTreeContent(const ListTTreeContent& other) = default;
        ListTTreeContent(const PosRBTree<T, MAX_LEAF_CAPACITY, TYPE_ID_POS_TREE_T>& postree) : tag{GC_SKIP_SLOTS}, postree{postree} { ; }
    };

    template<typename T, uint32_t TYPE_ID_POS_TREE_T>
    union ListTUnion
    {
        static_assert(sizeof(ListTInlineContent<T>) >= sizeof(ListTTreeContent<T, TYPE_ID_POS_TREE_T>));

        //empty list is inlinelist, upunning type type punning for assignment and default initialization
        std::array<uint8_t, sizeof(ListTInlineContent<T>)> upunning;
        ListTInlineContent<T> inlinelist;
        ListTTreeContent<T, TYPE_ID_POS_TREE_T> treelist;

        ListTUnion() : upunning{} { ; }
        ListTUnion(const ListTUnion& other) = default;

        ListTUnion(const ListTInlineContent<T>& c) : inlinelist{c} { ; }
        ListTUnion(const ListTTreeContent<T, TYPE_ID_POS_TREE_T>& c) : treelist{c} { ; }

        bool empty() const { return this->inlinelist.empty(); }

        bool isInline() const { return this->inlinelist.count < std::numeric_limits<uint32_t>::max(); }
        bool isTree() const { return this->inlinelist.count >= std::numeric_limits<uint32_t>::max(); }


        ListTUnion& operator=(const ListTUnion& other)
        {
            if(this == &other) {
                return *this;
            }

            this->upunning = other.upunning;
            return *this;
        }
    };

    template<typename T, uint32_t TYPE_ID_LIST_T>
    class ListStreamingBuilder
    {
    public:
        constexpr static size_t MAX_LEAF_CAPACITY = ListTTreeContent<T, TYPE_ID_LIST_T>::MAX_LEAF_CAPACITY;

        using LIST_T_INLINE = ListTInlineContent<T>;
        using LIST_T_TREE = ListTTreeContent<T, TYPE_ID_LIST_T>;
        using LIST_T_UNION = ListTUnion<T, TYPE_ID_LIST_T>;

        using POS_TREE_T = PosRBTree<T, MAX_LEAF_CAPACITY, TYPE_ID_LIST_T>;

        size_t pendingelements;
        std::array<T, MAX_LEAF_CAPACITY> pendingdata;

        size_t listsize;
        POS_TREE_T postree;

        ListStreamingBuilder() : pendingelements(0), pendingdata{}, listsize(0), postree{} {}

        void append(const T& v)
        {
            this->pendingdata[this->pendingelements++] = v;

            if(this->pendingelements == MAX_LEAF_CAPACITY) {
                if(this->listsize == 0) {
                    this->postree = POS_TREE_T::mkinitial(this->pendingdata.begin(), this->pendingdata.begin() + MAX_LEAF_CAPACITY);
                }
                else {
                    POS_TREE_T newleaf = POS_TREE_T::mkinitial(this->pendingdata.begin(), this->pendingdata.begin() + MAX_LEAF_CAPACITY);
                    this->postree = this->postree.builderPushBackLeafBlock(this->pendingdata, this->pendingelements);
                }

                this->listsize += this->pendingelements;
                
                this->pendingelements = 0;
                this->pendingdata.fill(T{});
            }
        }

        LIST_T_UNION finalize()
        {
            if(this->pendingelements == 0) {
                return LIST_T_UNION{};
            }
            else if(this->listsize == 0) {
                if(this->pendingelements <= LIST_T_INLINE::MAX_INLINE_CAPACITY) {                    
                    return LIST_T_UNION(LIST_T_INLINE(this->pendingdata.begin(), this->pendingelements));
                }
                else {
                    return LIST_T_UNION{LIST_T_TREE(POS_TREE_T::mkinitial(this->pendingdata.begin(), this->pendingdata.begin() + this->pendingelements))};
                }
            }
            else {
                return LIST_T_UNION(LIST_T_TREE{this->postree.builderPushBackLeafBlock(this->pendingdata, this->pendingelements)});
            }
        }
    };

    template<typename T>
    consteval TypeInfo g_typeinfo_ListTInlineContent_generate(uint32_t id, const char* mask, const char* name) 
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
            TypeOpDispatchInfo{},
            name,
            false
        };
    }

    template<typename T, uint32_t TYPE_ID_LIST_T>
    consteval TypeInfo g_typeinfo_ListTTreeContent(uint32_t id, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(ListTTreeContent<T, TYPE_ID_LIST_T>),
            byteSizeToSlotCount(sizeof(ListTTreeContent<T, TYPE_ID_LIST_T>)),
            LayoutTag::Value,
            "01",
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            TypeOpDispatchInfo{},
            name,
            false
        };
    }

    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    template<typename T, uint32_t TYPE_ID_LIST_T>
    class XListTIterator
    {
    public:
        int64_t index;
        ListTUnion<T, TYPE_ID_LIST_T> ulistt;

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
    public:
        constexpr static int64_t MAX_INLINE_CAPACITY = ListTInlineContent<T>::MAX_INLINE_CAPACITY;
        constexpr static int64_t MAX_LEAF_CAPACITY = ListTTreeContent<T, TYPE_ID_LIST_T>::MAX_LEAF_CAPACITY;

        using LIST_T_INLINE = ListTInlineContent<T>;
        using LIST_T_TREE = ListTTreeContent<T, TYPE_ID_LIST_T>;
        using LIST_T_UNION = ListTUnion<T, TYPE_ID_LIST_T>;

        using POS_TREE_T = PosRBTree<T, MAX_LEAF_CAPACITY, TYPE_ID_LIST_T>;

        LIST_T_UNION ulist;

        XList() : ulist{} {}
        XList(const XList& other) = default;
        XList(const LIST_T_INLINE& b) : ulist{b} { ; }
        XList(const POS_TREE_T& t) : ulist{LIST_T_TREE{t}} { ; }
        XList(const LIST_T_TREE& n) : ulist{n} { ; }
        XList(const LIST_T_UNION& u) : ulist{u} { ; }

        template<size_t len>
        XList(const T (&elems)[len]) : ulist{LIST_T_INLINE(elems, len)} { ; }

        static XList mk(std::initializer_list<T> elems)
        {
            if(elems.size() == 0) {
                return XList{};
            }
            else {
                if(elems.size() <= MAX_INLINE_CAPACITY) {
                    return XList{LIST_T_INLINE(elems.begin(), elems.end())};
                }
                else if(elems.size() <= MAX_LEAF_CAPACITY) {
                    return XList{POS_TREE_T::mkinitial(elems.begin(), elems.end())};
                }
                else {
                    return XList{POS_TREE_T::mklargerec(elems.begin(), elems.end(), elems.size())};
                }
            }
        }

        static XList mk(const T* elems, size_t len)
        {
            if(len == 0) {
                return XList{};
            }
            else {
                if(len <= MAX_INLINE_CAPACITY) {
                    return XList{LIST_T_INLINE(elems, len)};
                }
                else if(len <= MAX_LEAF_CAPACITY) {
                    return XList{POS_TREE_T::mkinitial(elems, elems + len)};
                }
                else {
                    return XList{POS_TREE_T::mklargerec(elems, elems + len, len)};
                }
            }
        }

        template<typename Iter>
        static XList mkspread(Iter start, Iter end, size_t len)
        {
            if(len == 0) {
                return XList{};
            }
            else {
                if(len <= MAX_INLINE_CAPACITY) {
                    return XList{LIST_T_INLINE(start, end)};
                }
                else if(len <= MAX_LEAF_CAPACITY) {
                    return XList{POS_TREE_T::mkinitial(start, end)};
                }
                else {
                    return XList{POS_TREE_T::mklargerec(start, end, len)};
                }
            }
        }

        bool empty() const
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

        XListTIterator<T, TYPE_ID_LIST_T> begin() const
        {
            return XListTIterator<T, TYPE_ID_LIST_T>{0, this->ulist};
        }

        XListTIterator<T, TYPE_ID_LIST_T> end() const
        {
            return XListTIterator<T, TYPE_ID_LIST_T>{(int64_t)this->size(), this->ulist};
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
                return XList{LIST_T_INLINE(value)};
            }
            else {
                if(this->ulist.isInline()) {
                    if(this->ulist.inlinelist.size() < MAX_INLINE_CAPACITY) {
                        return XList{LIST_T_INLINE(this->ulist.inlinelist, value)};
                    }
                    else {
                        return XList{POS_TREE_T::mkinitial(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count, value)};
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
                return XList{LIST_T_INLINE(value)};
            }
            else {
                if(this->ulist.isInline()) {
                    if(this->ulist.inlinelist.size() < MAX_INLINE_CAPACITY) {
                        return XList{LIST_T_INLINE(value, this->ulist.inlinelist)};
                    }
                    else {
                        return XList{POS_TREE_T::mkinitial(value, this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count)};
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
                return XList{LIST_T_INLINE(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + index, value, this->ulist.inlinelist.data.cbegin() + index + 1, this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count)};
            }
            else {
                return XList{this->ulist.treelist.postree.set(index, value)};
            }
        }

        XList insert(int64_t index, const T& value) const
        {
            if(this->ulist.empty()) {
                assert(index == 0);
                return XList{LIST_T_INLINE(value)};
            }
            else {
                if(this->ulist.isInline()) {
                    if(this->ulist.inlinelist.size() < MAX_INLINE_CAPACITY) {
                        return XList{LIST_T_INLINE(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + index, value, this->ulist.inlinelist.data.cbegin() + index, this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count)};
                    }
                    else {
                        return XList{POS_TREE_T::mkinitial(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + index, value, this->ulist.inlinelist.data.cbegin() + index, this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count)};
                    }
                }
                else {
                    return XList{this->ulist.treelist.postree.insert(index, value)};
                }
            }
        }

        XList deleteFront() const
        {
            if(this->ulist.isInline()) {
                if(this->ulist.inlinelist.count == 1) {
                    return XList{};
                }
                else {
                    return XList{LIST_T_INLINE(this->ulist.inlinelist.data.cbegin() + 1, this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count)};
                }
            }
            else {
                //if leaf type and size - 1 fits in inline repr
                if(this->ulist.treelist.postree.size() - 1 <= MAX_INLINE_CAPACITY && LIST_T_TREE::isLeafType(this->ulist.treelist.postree.root)) {
                    return XList{LIST_T_INLINE(this->ulist.treelist.postree.root->data.data.cbegin() + 1, this->ulist.treelist.postree.root->data.data.cbegin() + this->ulist.treelist.postree.root->data.dcount)};
                }
                else {
                    return XList{this->ulist.treelist.postree.deleteFront()};
                }
            }
        }

        XList deleteBack() const
        {
            if(this->ulist.isInline()) {
                if(this->ulist.inlinelist.count == 1) {
                    return XList{};
                }
                else {
                    return XList{LIST_T_INLINE(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count - 1)};
                }
            }
            else {
                //if leaf type and size - 1 fits in inline repr
                if(this->ulist.treelist.postree.size() - 1 <= MAX_INLINE_CAPACITY && LIST_T_TREE::isLeafType(this->ulist.treelist.postree.root)) {
                    return XList{LIST_T_INLINE(this->ulist.treelist.postree.root->data.data.cbegin(), this->ulist.treelist.postree.root->data.data.cbegin() + this->ulist.treelist.postree.root->data.dcount - 1)};
                }
                else {
                    return XList{this->ulist.treelist.postree.deleteBack()};
                }
            }
        }

        XList append(const XList& other) const
        {
            assert(!this->ulist.empty());
            assert(!other.ulist.empty());

            if(this->ulist.isInline() && other.ulist.isInline()) {
                if(this->ulist.inlinelist.size() + other.ulist.inlinelist.size() <= MAX_INLINE_CAPACITY) {
                    return XList{LIST_T_INLINE(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count, other.ulist.inlinelist.data.cbegin(), other.ulist.inlinelist.data.cbegin() + other.ulist.inlinelist.count)};
                }
                else {
                    if(this->ulist.inlinelist.size() + other.ulist.inlinelist.size() <= MAX_LEAF_CAPACITY) {
                        return XList{LIST_T_TREE{POS_TREE_T::mkinitial_append(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count, other.ulist.inlinelist.data.cbegin(), other.ulist.inlinelist.data.cbegin() + other.ulist.inlinelist.count)}};
                    }
                    else {
                        POS_TREE_T ll = POS_TREE_T::mkinitial(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count);
                        POS_TREE_T lr = POS_TREE_T::mkinitial(other.ulist.inlinelist.data.cbegin(), other.ulist.inlinelist.data.cbegin() + other.ulist.inlinelist.count);

                        return XList{POS_TREE_T::append(ll, lr)};
                    }
                }
            }
            else {
                POS_TREE_T lnode{};
                if(this->ulist.isInline()) {
                    lnode = POS_TREE_T::mkinitial(this->ulist.inlinelist.data.cbegin(), this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count);
                }
                else {
                    lnode = this->ulist.treelist.postree;
                }

                POS_TREE_T rnode{};
                if(other.ulist.isInline()) {
                    rnode = POS_TREE_T::mkinitial(other.ulist.inlinelist.data.cbegin(), other.ulist.inlinelist.data.cbegin() + other.ulist.inlinelist.count);
                }
                else {
                    rnode = other.ulist.treelist.postree;
                }

                return XList{POS_TREE_T::append(lnode, rnode)};
            }
        }

        template<typename U, uint32_t TYPE_ID_LIST_U>
        static XList<T, TYPE_ID_LIST_T> concat(const XList<U, TYPE_ID_LIST_U>& ll)
        {
            XList<T, TYPE_ID_LIST_T> curr{};

            for(auto ii = ll.begin(); ii != ll.end(); ++ii) {
                auto il = *ii;
                
                if(!il.empty()) {
                    if(curr.empty()) {
                        curr = il;
                    }
                    else {
                        curr = curr.append(il);
                    }
                }
            }

            return curr;
        }

        XList mk_mixed_append(const XList& other) const
        {
            if(this->ulist.empty()) {
                return other;
            }
            else if(other.ulist.empty()) {
                return *this;
            }
            else {
                return this->append(other);
            }
        }

        XBool contains(const T& v) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                auto ii = std::find_if(std::execution::unseq, ddbegin, ddend, [&v](const T& x){ return (bool)(x == v); });
                return XBool::from(ii != ddend);
            }
            else {
                return this->ulist.treelist.postree.contains(v);
            }
        }

        template<bool SafeSimplePred, typename Pred>
        XBool find(Pred p, T& res) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                typename std::array<T, MAX_INLINE_CAPACITY>::const_iterator ii;
                if constexpr (SafeSimplePred) {
                    ii = std::find_if(std::execution::unseq , ddbegin, ddend, p);
                }
                else {
                    ii = std::find_if(std::execution::seq, ddbegin, ddend, p);
                }

                if(ii == ddend) {
                    return XFALSE;
                }
                else {
                    res = *ii;
                    return XTRUE;
                }
            }
            else {
                return this->ulist.treelist.postree.template find<SafeSimplePred, Pred>(p, res);
            }
        }

        template<bool SafeSimplePred, typename Pred>
        XBool findIndex(Pred p, XNat& res) const
        {
            assert(!this->ulist.empty());

            assert(false); //NOT IMPLEMENTED YET!!!
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

                std::array<U, ListTTreeContent<U, TYPE_ID_LIST_U>::MAX_LEAF_CAPACITY> result{};
                std::transform(ddbegin, ddend, result.begin(), f);
                
                if(this->ulist.inlinelist.count <= ListTInlineContent<U>::MAX_INLINE_CAPACITY) {
                    return XList<U, TYPE_ID_LIST_U>{ListTInlineContent<U>(result.data(), this->ulist.inlinelist.count)};
                }
                else {
                    return XList<U, TYPE_ID_LIST_U>{PosRBTree<U, ListTTreeContent<U, TYPE_ID_LIST_U>::MAX_LEAF_CAPACITY, TYPE_ID_LIST_U>::mkinitial(result.data(), result.data() + this->ulist.inlinelist.count)};
                }
            }
            else {
                return XList<U, TYPE_ID_LIST_U>{this->ulist.treelist.postree.template map<SafeSimpleFn, U, TYPE_ID_LIST_U, Fn>(f)};
            }
        }

        template<bool SafeSimpleFn, typename U, uint32_t TYPE_ID_LIST_U, typename Fn>
        XList<U, TYPE_ID_LIST_U> mapIdx(Fn f) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                constexpr std::array<XNat, MAX_INLINE_CAPACITY> zipidx = create_idx_range<MAX_INLINE_CAPACITY>();

                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<U, ListTTreeContent<U, TYPE_ID_LIST_U>::MAX_LEAF_CAPACITY> result{};
                std::transform(ddbegin, ddend, zipidx.begin(), result.begin(), f);
                
                if(this->ulist.inlinelist.count <= ListTInlineContent<U>::MAX_INLINE_CAPACITY) {
                    return XList<U, TYPE_ID_LIST_U>{ListTInlineContent<U>(result.data(), this->ulist.inlinelist.count)};
                }
                else {
                    return XList<U, TYPE_ID_LIST_U>{PosRBTree<U, ListTTreeContent<U, TYPE_ID_LIST_U>::MAX_LEAF_CAPACITY, TYPE_ID_LIST_U>::mkinitial(result.data(), result.data() + this->ulist.inlinelist.count)};
                }
            }
            else {
                return XList<U, TYPE_ID_LIST_U>{this->ulist.treelist.postree.template mapIdx<SafeSimpleFn, U, TYPE_ID_LIST_U, Fn>(f)};
            }
        }

        template<bool SafeSimpleFn, typename Pred>
        XList<T, TYPE_ID_LIST_T> filter(Pred p) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<T, MAX_LEAF_CAPACITY> result{};
                auto eiter = std::copy_if(ddbegin, ddend, result.begin(), p);
                
                if(eiter == result.begin()) {
                    return XList<T, TYPE_ID_LIST_T>{};
                }
                else {
                    return XList<T, TYPE_ID_LIST_T>{LIST_T_INLINE(result.data(), std::distance(result.begin(), eiter))};
                }
            }
            else {
                ListStreamingBuilder<T, TYPE_ID_LIST_T> builder{};
                
                for(auto iter = this->begin(); iter != this->end(); ++iter) {
                    T val = *iter;
                    
                    if(p(val)) {
                        builder.append(val);
                    }
                }

                return XList<T, TYPE_ID_LIST_T>{builder.finalize()};
            }
        }

        template<bool BothSafeSimpleFn, typename U, uint32_t TYPE_ID_LIST_U, typename Pred, typename Fn>
        XList<U, TYPE_ID_LIST_U> filtermap(Pred p, Fn f) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<T, MAX_LEAF_CAPACITY> fresult{};
                auto feiter = std::copy_if(ddbegin, ddend, fresult.begin(), p);

                if(feiter == fresult.begin()) {
                    return XList<U, TYPE_ID_LIST_U>{};
                }
                else {
                    std::array<U, ListTTreeContent<U, TYPE_ID_LIST_U>::MAX_LEAF_CAPACITY> mresult{};
                    auto meiter = std::transform(fresult.begin(), feiter, mresult.begin(), f);
                    
                    if(std::distance(mresult.begin(), meiter) < ListTInlineContent<U>::MAX_INLINE_CAPACITY) {
                        return XList<U, TYPE_ID_LIST_U>{ListTInlineContent<U>(mresult.data(), std::distance(mresult.begin(), meiter))};
                    }
                    else {
                        return XList<U, TYPE_ID_LIST_U>{PosRBTree<U, ListTTreeContent<U, TYPE_ID_LIST_U>::MAX_LEAF_CAPACITY, TYPE_ID_LIST_U>::mkinitial(mresult.data(), mresult.data() + std::distance(mresult.begin(), meiter))};
                    }
                }
            }
            else {
                ListStreamingBuilder<U, TYPE_ID_LIST_U> builder{};

                for(auto iter = this->begin(); iter != this->end(); ++iter) {
                    T val = *iter;

                    if(p(val)) {
                        builder.append(f(val));
                    }
                }

                return XList<U, TYPE_ID_LIST_U>{builder.finalize()};
            }
        }

        template<bool SafeSimpleFn, typename Cmp>
        T minfun(Cmp cmp) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                if constexpr (SafeSimpleFn) {
                    return *std::min_element(std::execution::unseq, ddbegin, ddend, cmp);
                }
                else {
                    return *std::min_element(std::execution::seq, ddbegin, ddend, cmp);
                }
            }
            else {
                return this->ulist.treelist.postree.template minfun<SafeSimpleFn>(cmp);
            }
        }

        template<bool SafeSimpleFn, typename Cmp>
        T maxfun(Cmp cmp) const
        {
            assert(!this->ulist.empty());

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                if constexpr (SafeSimpleFn) {
                    return *std::max_element(std::execution::unseq, ddbegin, ddend, cmp);
                }
                else {
                    return *std::max_element(std::execution::seq, ddbegin, ddend, cmp);
                }
            }
            else {
                return this->ulist.treelist.postree.template maxfun<SafeSimpleFn>(cmp);
            }
        }

        T sum() const
        {
            if(this->ulist.empty()) {
                return T{};
            }

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                return std::accumulate(ddbegin, ddend, T{}, [](T a, T b) {
                    T::checkOverflowAddition(a, b, "List Sum", 0);
                    return a + b;
                });
            }
            else {
                return this->ulist.treelist.postree.sum();
            }
        }

        XList<T, TYPE_ID_LIST_T> sumprefix() const
        {
            if(this->ulist.empty()) {
                return XList<T, TYPE_ID_LIST_T>{};
            }

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                std::array<T, MAX_LEAF_CAPACITY> result{};
                std::partial_sum(ddbegin, ddend, result.begin(), [](T a, T b) { T::checkOverflowAddition(a, b, "List Prefix Sum", 0); return a + b; });

                return XList<T, TYPE_ID_LIST_T>{LIST_T_INLINE(result.data(), this->ulist.inlinelist.count)};
            }
            else {
                return XList<T, TYPE_ID_LIST_T>{this->ulist.treelist.postree.sumprefix()};
            }
        }

        template<bool SafeSimpleFn, typename Fn>
        T reduce(const T& acc, Fn op) const
        {
            if(this->ulist.empty()) {
                return acc;
            }

            if(this->ulist.isInline()) {
                auto ddbegin = this->ulist.inlinelist.data.cbegin();
                auto ddend = this->ulist.inlinelist.data.cbegin() + this->ulist.inlinelist.count;

                return std::accumulate(ddbegin, ddend, acc, [&op](const T& a, const T& b) {
                    return op(a, b);
                });
            }
            else {
                return this->ulist.treelist.postree.template reduce<SafeSimpleFn>(acc, op);
            }
        }
    };

    template<typename T, uint32_t TYPE_ID_LIST_T>
    void jsonParseToBSQ_ListT(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array(), "JSON -> BSQ", 0, nullptr, "Expected JSON array List<T>");

        T val;
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        ListStreamingBuilder<T, TYPE_ID_LIST_T> builder;
        for(size_t i = 0; i < j.size(); i++) {
            ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j[i], &val);
            builder.append(val);
        }

        *(XList<T, TYPE_ID_LIST_T>*)resptr = XList<T, TYPE_ID_LIST_T>{builder.finalize()};
    }

    template<typename T, uint32_t TYPE_ID_LIST_T>
    void parseToBSQ_ListT(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected type for List<T>");
        lexer->consume();
        bsq_validate(lexer->testIsSymbol('{'), "BAPI -> BSQ", 0, nullptr, "Expected '{' for List<T>");
        lexer->consume();

        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ListStreamingBuilder<T, TYPE_ID_LIST_T> builder;

        bool first = true;
        while(!lexer->testIsSymbol('}')) {
            if(first) {
                first = false;
            }
            else {
                bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' between elements for List<T>");
                lexer->consume();
            }
            
            T val;
            ofinfo->opdispatch.parseToBSQFp(ofinfo, lexer, &val);
            builder.append(val);
        }

        bsq_validate(lexer->testIsSymbol('}'), "BAPI -> BSQ", 0, nullptr, "Expected '}' for List<T>");
        lexer->consume();

        *(XList<T, TYPE_ID_LIST_T>*)resptr = XList<T, TYPE_ID_LIST_T>{builder.finalize()};
    }

    template<typename T, uint32_t TYPE_ID_LIST_T>
    json bsqToJSON_ListT(const TypeInfo* tinfo, const void* valptr)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        json j = json::array();
        const XList<T, TYPE_ID_LIST_T>* list = (const XList<T, TYPE_ID_LIST_T>*)valptr;
        for(auto iter = list->begin(); iter != list->end(); ++iter) {
            T val = *iter;
            j.push_back(ofinfo->opdispatch.bsqToJSONFp(ofinfo, &val));
        }

        return j;

    }

    template<typename T, uint32_t TYPE_ID_LIST_T>
    void bsqToBAPI_ListT(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const XList<T, TYPE_ID_LIST_T>* list = (const XList<T, TYPE_ID_LIST_T>*)valptr;
        
        builder->appendConstString(tinfo->typekey);

        if(list->empty()) {
            builder->appendLiteralString("{ }");
            return;
        }
        else {
            builder->appendLiteralString("{ ");

            bool first = true;
            for(auto iter = list->begin(); iter != list->end(); ++iter) {
                if(first) {
                    first = false;
                }
                else {
                    builder->appendLiteralString(", ");
                }

                T val = *iter;
                ofinfo->opdispatch.bsqToBAPIFp(ofinfo, &val, builder);
            }

            builder->appendLiteralString(" }");
        }
    }
    
    template<typename T, uint32_t TYPE_ID_LIST_T>
    void displayValue_ListT(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const XList<T, TYPE_ID_LIST_T>* list = (const XList<T, TYPE_ID_LIST_T>*)valptr;

        os << getDisplayIndent(indent) << tinfo->typekey << "{ ";
        
        if(list->empty()) {
            os << getDisplayIndent(indent) << tinfo->typekey << "{ }";
            return;
        }
        else {
            bool first = true;
            for(auto iter = list->begin(); iter != list->end(); ++iter) {
                if(first) {
                    first = false;
                }
                else {
                    os << ", ";
                }

                T val = *iter;
                ofinfo->opdispatch.displayFp(ofinfo, &val, os, indent);
            }
            os << " }";
        }
    }

    template<typename T, uint32_t TYPE_ID_LIST_T>
    consteval TypeInfo g_typeinfo_ListT_generate(uint32_t id, const TypeLayoutInfo* layout, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            sizeof(XList<T, TYPE_ID_LIST_T>),
            byteSizeToSlotCount(sizeof(XList<T, TYPE_ID_LIST_T>)),
            LayoutTag::Value,
            mask,
            nullptr,
            0,
            layout,
            1,
            nullptr,
            0,
            TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_ListT<T, TYPE_ID_LIST_T>, (ParseToBSQFp)&parseToBSQ_ListT<T, TYPE_ID_LIST_T>, (BSQToJSONFp)&bsqToJSON_ListT<T, TYPE_ID_LIST_T>, (BSQToBAPIFp)&bsqToBAPI_ListT<T, TYPE_ID_LIST_T>, (DisplayValueFp)&displayValue_ListT<T, TYPE_ID_LIST_T> },
            name,
            false
        };
    }

    namespace XListOps 
    {
        template <typename T, uint32_t TYPE_ID_LIST_T>
        XList<T, TYPE_ID_LIST_T> fromRange(int64_t start, int64_t end, int64_t step, bool inclusive)
        {
            int64_t count = ((end - start) / step) + ((inclusive || (((end - start) % step) != 0)) ? 1 : 0);
            auto gen = [curr = start, step]() mutable { int64_t ret = curr; curr += step; return T{ret}; };

            if(count <= 0) {
                return XList<T, TYPE_ID_LIST_T>{};
            }
            else if(count <= ListTInlineContent<T>::MAX_INLINE_CAPACITY) {
                std::array<T, ListTInlineContent<T>::MAX_INLINE_CAPACITY> result{};
                std::generate(result.begin(), result.begin() + count, gen);

                return XList<T, TYPE_ID_LIST_T>{ListTInlineContent<T>(result.data(), count)};
            }
            else if(count <= XList<T, TYPE_ID_LIST_T>::MAX_LEAF_CAPACITY) {
                std::array<T, XList<T, TYPE_ID_LIST_T>::MAX_LEAF_CAPACITY> result{};
                std::generate(result.begin(), result.begin() + count, gen);

                return XList<T, TYPE_ID_LIST_T>{PosRBTree<T, XList<T, TYPE_ID_LIST_T>::MAX_LEAF_CAPACITY, TYPE_ID_LIST_T>::mkinitial(result.data(), result.data() + count)};
            }
            else {
                int64_t curr = start;
                return XList<T, TYPE_ID_LIST_T>{PosRBTree<T, XList<T, TYPE_ID_LIST_T>::MAX_LEAF_CAPACITY, TYPE_ID_LIST_T>::mkrange(count, curr, step)};
            }
        }

        template <typename J, uint32_t TYPE_ID_LIST_J, typename ListT, typename ListU>
        XList<J, TYPE_ID_LIST_J> zip(const ListT& l1, const ListU& l2, int64_t ssize)
        {
            if(ssize < ListTInlineContent<J>::MAX_INLINE_CAPACITY) {
                std::array<J, ListTInlineContent<J>::MAX_INLINE_CAPACITY> result{};
                std::transform(l1.ulist.inlinelist.data.cbegin(), l1.ulist.inlinelist.data.cbegin() + ssize, l2.ulist.inlinelist.data.cbegin(), result.begin(), [](const auto& a, const auto& b) { return J{a, b}; });

                return XList<J, TYPE_ID_LIST_J>{ListTInlineContent<J>(result.data(), ssize)};
            }
            else {
                return XList<J, TYPE_ID_LIST_J>{PosRBTree<J, XList<J, TYPE_ID_LIST_J>::MAX_LEAF_CAPACITY, TYPE_ID_LIST_J>::mkzip(l1.begin(), l2.begin(), ssize)};
            }
        }

        template<typename T, typename StrList>
        static T concatStrs(const StrList& ll)
        {
            T curr{};

            for(auto ii = ll.begin(); ii != ll.end(); ++ii) {
                auto il = *ii;
                
                if(!il.empty()) {
                    if(curr.empty()) {
                        curr = il;
                    }
                    else {
                        curr = curr.append(il);
                    }
                }
            }

            return curr;
        }

        template<typename T, typename StrList>
        static T joinStrs(const T& sep, const StrList& ll)
        {
            T curr{};

            bool first = true;
            for(auto ii = ll.begin(); ii != ll.end(); ++ii) {
                auto il = *ii;
                
                if(!first) {
                    if(curr.empty()) {
                        curr = sep;
                    }
                    else {
                        curr = curr.append(sep);
                    }
                }
                first = false;

                if(!il.empty()) {
                    if(curr.empty()) {
                        curr = il;
                    }
                    else {
                        curr = curr.append(il);
                    }
                }
            }

            return curr;
        }

        template<typename Iter>
        static std::pair<Iter, Iter> wstrimHelper(bool dotrim, Iter start, Iter end)
        {
            if(!dotrim) {
                return {start, end};
            }

            while(start != end && isTrimableWhitespace(*start)) {
                ++start;
            }

            if(start == end) {
                return {start, end};
            }

            --end;
            while(isTrimableWhitespace(*end)) {
                --end;
            }
            ++end;

            return {start, end};
        }

        template<typename CharType, typename StrType, typename StrList>
        static StrList splitStrsChar(const StrType& str, const CharType& sep, bool trim, bool dropempty)
        {
            if(str.empty()) {
                if(dropempty) {
                    return StrList{};
                }
                else {
                    return StrList{StrType{}};
                }
            }

            StrList res{};

            auto curr = str.begin();
            auto end = str.end();
    
            while(curr != end) {
                auto next = std::find(curr, end, sep.value);
                auto [a, b] = wstrimHelper(trim, curr, next);

                if(a != b || !dropempty) {
                    StrType part = StrType::mk(a, b, std::distance(a, b));
                    res = res.pushBack(part);
                }
                curr = next;

                if(curr != end) {
                    ++curr;
                    if(curr == end && !dropempty) {
                        res = res.pushBack(StrType{}); //"ab" with b should be ["a", ""] <-empty at end
                    }
                }
            }

            return res;
        }

        template<typename CharType, typename StrType, typename StrList>
        static StrList splitStrsString(const StrType& str, const StrType& sep, bool trim, bool dropempty)
        {
            if(str.empty()) {
                if(dropempty) {
                    return StrList{};
                }
                else {
                    return StrList{StrType{}};
                }
            }

            auto sepsize = sep.size();
            auto curr = str.begin();
            auto end = str.end();

            if(sep.size() == 0) {
                StrList res{};
                while(curr != end) {
                    auto cpos = curr;
                    ++curr;

                    if(!isTrimableWhitespace(*cpos)) {
                        res = res.pushBack(StrType::mk(cpos, curr, 1));
                    }
                    else {
                        if(!dropempty) {
                            if(trim) {
                                res = res.pushBack(StrType{});
                            }
                            else {
                                res = res.pushBack(StrType::mk(cpos, curr, 1));
                            }
                        }
                    }
                }
                return res;
            }
            else if(sepsize == 1) {
                //faster to match single char
                return splitStrsChar<CharType, StrType, StrList>(str, CharType{*sep.begin()}, trim, dropempty);
            }
            else {
                StrList res{};

                while(curr != end) {
                    auto next = std::search(curr, end, sep.begin(), sep.end());
                    auto [a, b] = wstrimHelper(trim, curr, next);

                    if(a != b || !dropempty) {
                        StrType part = StrType::mk(a, b, std::distance(a, b));
                        res = res.pushBack(part);
                    }
                    curr = next;

                    if(curr != end) {
                        for(int64_t i = 0; i < sepsize; ++i) {
                            ++curr;
                        }

                        if(curr == end && !dropempty) {
                            res = res.pushBack(StrType{}); //"ab" with b should be ["a", ""] <-empty at end
                        }
                    }
                }

                return res;
            }
        }

        template<typename StrType, typename StrList, typename FnReMatchPosLen>
        static StrList splitStrsRegex(const StrType& str, bool trim, bool dropempty, const FnReMatchPosLen& mfn)
        {
            if(str.empty()) {
                if(dropempty) {
                    return StrList{};
                }
                else {
                    return StrList{StrType{}};
                }
            }

            StrList res{};

            auto curr = str.begin();
            auto end = str.end();

            while(curr != end) {
                auto [next, matchlen] = mfn(curr, end);
                if(next != end && matchlen == 0) {
                    auto cpos = curr;
                    ++curr;

                    if(!isTrimableWhitespace(*cpos)) {
                        res = res.pushBack(StrType::mk(cpos, curr, 1));
                    }
                    else {
                        if(!dropempty) {
                            if(trim) {
                                res = res.pushBack(StrType{});
                            }
                            else {
                                res = res.pushBack(StrType::mk(cpos, curr, 1));
                            }
                        }
                    }
                }
                else {
                    auto [a, b] = wstrimHelper(trim, curr, next);

                    if(a != b || !dropempty) {
                        StrType part = StrType::mk(a, b, std::distance(a, b));
                        res = res.pushBack(part);
                    }
                    curr = next;

                    if(curr != end) {
                       for(size_t i = 0; i < matchlen; ++i) {
                            ++curr;
                        }
                    }

                    if(curr == end && matchlen != 0 && !dropempty) {
                       res = res.pushBack(StrType{}); //"ab" with b should be ["a", ""] <-empty at end
                    }
                }
            }

            return res;
        }
    }

    inline bool gcIsListTInline(void** ptr) { return *((size_t*)ptr) < std::numeric_limits<uint32_t>::max(); }
    inline size_t gcGetListTInlineSkipCount(void** ptr) { return *((size_t*)ptr) - std::numeric_limits<uint32_t>::max(); }
}

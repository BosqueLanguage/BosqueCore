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
        constexpr static int64_t CSTR_BUFF_SIZE = 16;
        constexpr static int64_t CSTR_MAX_SIZE = CSTR_BUFF_SIZE - 1;

        char data[CSTR_BUFF_SIZE];

        constexpr CStrRootInlineContent() : data{0} {}
        constexpr CStrRootInlineContent(const CStrRootInlineContent& other) = default;

        constexpr bool empty() const { return static_cast<int64_t>(this->data[0]) == 0; }

        template<size_t len>
        constexpr static CStrRootInlineContent literal(const char (&cstr)[len])
        {
            static_assert(len - 1 != 0, "CString inline literal should not be empty");
            static_assert(len - 1 <= ᐸRuntimeᐳ::CStrRootInlineContent::CSTR_MAX_SIZE, "CString literal too large for CStrRootInlineContent");

            CStrRootInlineContent cb;
            cb.data[0] = static_cast<char>(len - 1); //store length
            std::copy(cstr, cstr + len - 1, cb.data + 1);

            return cb;
        }

        static CStrRootInlineContent literaldynamic(const char* cstr, size_t len)
        {
            assert(len != 0);
            assert(len <= ᐸRuntimeᐳ::CStrRootInlineContent::CSTR_MAX_SIZE);

            CStrRootInlineContent cb;
            cb.data[0] = static_cast<char>(len); //store length
            std::copy(cstr, cstr + len, cb.data + 1);

            return cb;
        }

        constexpr int64_t size() const { return static_cast<int64_t>(this->data[0]); }
        constexpr char at(int64_t index) const { return this->data[index + 1]; }
    };

    class CStrRootTreeContent
    {
    public:
        constexpr static int64_t CSTR_MAX_LEAF_SIZE = CStrRootInlineContent::CSTR_BUFF_SIZE * 2;

        PosRBTree<char, CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING> postree;
    };

    inline constexpr TypeInfo g_typeinfo_PosRBTreeLeaf_CString = g_typeinfo_PosRBTreeLeaf_generate<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_CSTRING, BSQ_PTR_MASK_LEAF, "PosRBTreeLeaf_CString");
    inline constexpr TypeInfo g_typeinfo_PosRBTreeNode_CString = g_typeinfo_PosRBTreeNode_generate<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_CSTRING, "PosRBTreeNode_CString");
    inline constexpr TypeInfo g_typeinfo_PosRBTree_CString = g_typeinfo_PosRBTree_generate<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>(WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING, "PosRBTree_CString");

    extern thread_local GCAllocator<PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeLeaf_CString_allocator;
    extern thread_local GCAllocator<PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeNode_CString_allocator;

    union CStringUnion
    {
        //empty cstring is where boxed union typeinfo is nullptr
        CStrRootInlineContent inlinecstr;
        CStrRootTreeContent treecstr;

        constexpr CStringUnion() : inlinecstr() {}
        constexpr CStringUnion(const CStringUnion& other) = default;
        constexpr CStringUnion(const CStrRootInlineContent& c) : inlinecstr(c) {}
        constexpr CStringUnion(const CStrRootTreeContent& c) : treecstr(c) {}
    };

    inline constexpr TypeInfo g_typeinfo_CStringInline = {
        WELL_KNOWN_TYPE_ID_CSTRING_INLINE,
        sizeof(CStrRootInlineContent),
        byteSizeToSlotCount(sizeof(CStrRootInlineContent)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "CStringInline",
        nullptr
    };

    inline constexpr TypeInfo g_typeinfo_CStringTree = {
        WELL_KNOWN_TYPE_ID_CSTRING_TREE,
        sizeof(CStrRootTreeContent),
        byteSizeToSlotCount(sizeof(CStrRootTreeContent)),
        LayoutTag::Tagged,
        "20",
        "CStringTree",
        nullptr
    };

    inline constexpr TypeInfo g_typeinfo_CString = {
        WELL_KNOWN_TYPE_ID_CSTRING,
        sizeof(BoxedUnion<CStringUnion>),
        byteSizeToSlotCount(sizeof(BoxedUnion<CStringUnion>)),
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
        BoxedUnion<CStringUnion> ucstr;

        using value_type = char;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(this->ucstr.typeinfo != nullptr); //should not dereference on empty string

            if(this->ucstr.typeinfo == &g_typeinfo_CStringInline) {
                return this->ucstr.data.inlinecstr.at(this->index);
            }
            else {
                return this->ucstr.data.treecstr.postree.get(this->index);
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
        BoxedUnion<CStringUnion> ucstr;

    public:
        constexpr XCString() : ucstr() {}
        constexpr XCString(const CStrRootInlineContent& b) : ucstr(BoxedUnion<CStringUnion>(&g_typeinfo_CStringInline, CStringUnion(b))) {}
        constexpr XCString(CStrRootTreeContent& n) : ucstr(BoxedUnion<CStringUnion>(&g_typeinfo_CStringTree, CStringUnion(n))) {}
        constexpr XCString(const XCString& other) = default;

        template<size_t len>
        constexpr static XCString smliteral(const char (&cstr)[len])
        {
            static_assert(len - 1 <= CStrRootInlineContent::CSTR_MAX_SIZE, "CString literal too large for CStrRootInlineContent");

            return XCString(CStrRootInlineContent::literal(cstr));
        }

        constexpr static XCString smliteral(const char (&cstr)[1])
        {
            return XCString();
        }

        static XCString smliteraldynamic(const char* cstr, size_t len)
        {
            assert(len <= CStrRootInlineContent::CSTR_MAX_SIZE);

            if(len == 0) {
                return XCString();
            }
            else {
                return XCString(CStrRootInlineContent::literaldynamic(cstr, len));
            }
        }

        bool empty() const
        {
            return this->ucstr.typeinfo == nullptr;
        }

        int64_t size() const
        {
            if(this->ucstr.typeinfo == nullptr) {
                return 0;
            }
            else {
                if(this->ucstr.typeinfo == &g_typeinfo_CStringInline) {
                    return this->ucstr.data.inlinecstr.size();
                }
                else {
                    return this->ucstr.data.treecstr.postree.count();
                }
            }
        }

        int64_t bytes() const
        {
            return this->size() * sizeof(char);
        }

        XCStringIterator begin() const
        {
            return XCStringIterator{0, this->ucstr};
        }

        XCStringIterator end() const
        {
            return XCStringIterator{(int64_t)this->size(), this->ucstr};
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

    class XFCStringRepr 
    {
    public:
        std::vector<std::pair<uint8_t, const char*>> strcomps;
        
        int64_t cmpsize;
        size_t fcid;
    };

    class XFCString
    {
    public:
        size_t fcid;

        static std::vector<XFCStringRepr> g_formatStringReprs;

        template<size_t K>
        static XCString interpolate(size_t reprid, std::array<XCString, K> cstr)
        {
            const XFCStringRepr& repr = XFCString::g_formatStringReprs[reprid];
            
            int64_t total_size = repr.cmpsize;
            for(size_t i = 0; i < repr.strcomps.size(); i++) {
                if(repr.strcomps[i].second == nullptr) {
                    uint8_t argpos = repr.strcomps[i].first;

                    assert(argpos < K);
                    total_size += cstr[argpos].size();
                }
            }

            if(total_size <= CStrRootInlineContent::CSTR_MAX_SIZE) {
                char inlined[total_size + 1] = {0};
                char* ptr = inlined;

                for(size_t i = 0; i < repr.strcomps.size(); i++) {
                    const std::pair<uint8_t, const char*>& comp = repr.strcomps[i];
                    if(comp.second != nullptr) {
                        size_t cmp_size = std::char_traits<char>::length(comp.second);
                        std::copy(comp.second, comp.second + cmp_size, ptr);
                        ptr += cmp_size;
                    }
                    else {
                        uint8_t argpos = comp.first;
                        std::copy(cstr[argpos].begin(), cstr[argpos].end(), ptr);
                        ptr += cstr[argpos].size();
                    }
                }
                
                return XCString::smliteraldynamic(inlined, total_size);
            }
            else {
                assert(false); // Not Implemented: full support for FString interpolation
            }
        }
    };

    class StrRootInlineContent
    {
    public:
        constexpr static int64_t STR_BUFF_SIZE = 8;
        constexpr static int64_t STR_MAX_SIZE = STR_BUFF_SIZE - 1;

        char32_t data[STR_BUFF_SIZE];

        constexpr StrRootInlineContent() : data{0} {}
        constexpr StrRootInlineContent(const StrRootInlineContent& other) = default;

        constexpr bool empty() const { return static_cast<int64_t>(this->data[0]) == 0; }

        template<size_t len>
        constexpr static StrRootInlineContent literal(const char32_t (&str)[len])
        {
            static_assert(len - 1 != 0, "String literal cannot be empty");
            static_assert(len - 1 <= ᐸRuntimeᐳ::StrRootInlineContent::STR_MAX_SIZE, "String literal too large for StrRootInlineContent");

            StrRootInlineContent cb;
            cb.data[0] = static_cast<uint32_t>(len - 1); //store length
            std::copy(str, str + len - 1, cb.data + 1);

            return cb;
        }

        static StrRootInlineContent literaldynamic(const char32_t* str, size_t len)
        {
            assert(len != 0);
            assert(len <= ᐸRuntimeᐳ::StrRootInlineContent::STR_MAX_SIZE);

            StrRootInlineContent cb;
            cb.data[0] = static_cast<uint32_t>(len); //store length
            std::copy(str, str + len, cb.data + 1);

            return cb;
        }

        constexpr int64_t size() const { return static_cast<int64_t>(this->data[0]); }
        constexpr char32_t at(int64_t index) const { return this->data[index + 1]; }
    };

    class StrRootTreeContent
    {
    public:
        constexpr static int64_t STR_MAX_LEAF_SIZE = StrRootInlineContent::STR_BUFF_SIZE * 2;

        PosRBTree<char32_t, STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING> postree;
    };

    inline constexpr TypeInfo g_typeinfo_PosRBTreeLeaf_String = g_typeinfo_PosRBTreeLeaf_generate<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_STRING, BSQ_PTR_MASK_LEAF, "PosRBTreeLeaf_String");
    inline constexpr TypeInfo g_typeinfo_PosRBTreeNode_String = g_typeinfo_PosRBTreeNode_generate<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_STRING, "PosRBTreeNode_String");
    inline constexpr TypeInfo g_typeinfo_PosRBTree_String = g_typeinfo_PosRBTree_generate<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>(WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING, "PosRBTree_String");

    extern thread_local GCAllocator<PosRBTreeLeaf<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeLeaf_String_allocator;
    extern thread_local GCAllocator<PosRBTreeNode<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeNode_String_allocator;

    union StringUnion
    {
        //empty string is where boxed union typeinfo is nullptr
        StrRootInlineContent inlinecstr;
        StrRootTreeContent treecstr;

        constexpr StringUnion() : inlinecstr() {}
        constexpr StringUnion(const StringUnion& other) = default;
        constexpr StringUnion(const StrRootInlineContent& c) : inlinecstr(c) {}
        constexpr StringUnion(const StrRootTreeContent& c) : treecstr(c) {}
    };

    inline constexpr TypeInfo g_typeinfo_StringInline = {
        WELL_KNOWN_TYPE_ID_STRING_INLINE,
        sizeof(StrRootInlineContent),
        byteSizeToSlotCount(sizeof(StrRootInlineContent)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "StringInline",
        nullptr
    };

    inline constexpr TypeInfo g_typeinfo_StringTree = {
        WELL_KNOWN_TYPE_ID_STRING_TREE,
        sizeof(StrRootTreeContent),
        byteSizeToSlotCount(sizeof(StrRootTreeContent)),
        LayoutTag::Tagged,
        "20",
        "StringTree",
        nullptr
    };

    inline constexpr TypeInfo g_typeinfo_String = {
        WELL_KNOWN_TYPE_ID_STRING,
        sizeof(BoxedUnion<StringUnion>),
        byteSizeToSlotCount(sizeof(BoxedUnion<StringUnion>)),
        LayoutTag::Tagged,
        "20000",
        "String",
        nullptr
    };

    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    class XStringIterator
    {
    public:
        int64_t index;
        BoxedUnion<StringUnion> ustr;

        using value_type = char32_t;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(this->ustr.typeinfo != nullptr); //should not dereference on empty string

            if(this->ustr.typeinfo == &g_typeinfo_StringInline) {
                return this->ustr.data.inlinecstr.at(this->index);
            }
            else {
                return this->ustr.data.treecstr.postree.get(this->index);
            }
        }

        XStringIterator& operator++()
        {
            this->index++;
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
        BoxedUnion<StringUnion> ustr;

    public:
        constexpr XString() : ustr() {}
        constexpr XString(const StrRootInlineContent& b) : ustr(BoxedUnion<StringUnion>(&g_typeinfo_StringInline, StringUnion(b))) {}
        constexpr XString(StrRootTreeContent& n) : ustr(BoxedUnion<StringUnion>(&g_typeinfo_StringTree, StringUnion(n))) {}
        constexpr XString(const XString& other) = default;

        template<size_t len>
        constexpr static XString smliteral(const char32_t (&str)[len])
        {
            static_assert(len - 1 <= StrRootInlineContent::STR_MAX_SIZE, "String literal too large for StrRootInlineContent");

            return XString(StrRootInlineContent::literal(str));
        }

        constexpr static XString smliteral(const char32_t (&str)[1])
        {
            return XString();
        }

        static XString smliteraldynamic(const char32_t* str, size_t len)
        {
            assert(len <= StrRootInlineContent::STR_MAX_SIZE);

            if(len == 0) {
                return XString();
            }
            else {
                return XString(StrRootInlineContent::literaldynamic(str, len));
            }
        }

        bool empty() const
        {
            return this->ustr.typeinfo == nullptr;
        }

        int64_t size() const
        {
            if(this->ustr.typeinfo == nullptr) {
                return 0;
            }
            else {
                if(this->ustr.typeinfo == &g_typeinfo_StringInline) {
                    return this->ustr.data.inlinecstr.size();
                }
                else {
                    return this->ustr.data.treecstr.postree.count();
                }
            }
        }

        int64_t bytes() const
        {
            return this->size() * sizeof(char32_t);
        }

        XStringIterator begin() const
        {
            return XStringIterator{0, this->ustr};
        }

        XStringIterator end() const
        {
            return XStringIterator{(int64_t)this->size(), this->ustr};
        }

        friend XBool operator==(const XString& lhs, const XString& rhs) 
        { 
            return XBool::from(std::equal(lhs.begin(), lhs.end(), rhs.begin())); 
        }

        friend XBool operator<(const XString& lhs, const XString& rhs) 
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

        friend XBool operator>(const XString& lhs, const XString& rhs) 
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
        
        friend XBool operator!=(const XString& lhs, const XString& rhs) { return !(lhs == rhs); }
        friend XBool operator<=(const XString& lhs, const XString& rhs) { return !(lhs > rhs); }
        friend XBool operator>=(const XString& lhs, const XString& rhs) { return !(lhs < rhs); }
    };

    class XFStringRepr 
    {
    public:
        std::vector<std::pair<uint8_t, const char32_t*>> strcomps;
        
        int64_t cmpsize;
        size_t fcid;
    };

    class XFString
    {
    public:
        size_t fcid;

        static std::vector<XFStringRepr> g_formatStringReprs;

        template<size_t K>
        static XString interpolate(size_t reprid, std::array<XString, K> cstr)
        {
            const XFStringRepr& repr = XFString::g_formatStringReprs[reprid];
            
            int64_t total_size = repr.cmpsize;
            for(size_t i = 0; i < repr.strcomps.size(); i++) {
                if(repr.strcomps[i].second == nullptr) {
                    uint8_t argpos = repr.strcomps[i].first;

                    assert(argpos < K);
                    total_size += cstr[argpos].size();
                }
            }

            if(total_size <= StrRootInlineContent::STR_MAX_SIZE) {
                char32_t inlined[total_size + 1] = {0};
                char32_t* ptr = inlined;

                for(size_t i = 0; i < repr.strcomps.size(); i++) {
                    const std::pair<uint8_t, const char32_t*>& comp = repr.strcomps[i];
                    if(comp.second != nullptr) {
                        size_t cmp_size = std::char_traits<char32_t>::length(comp.second);
                        std::copy(comp.second, comp.second + cmp_size, ptr);
                        ptr += cmp_size;
                    }
                    else {
                        uint8_t argpos = comp.first;
                        std::copy(cstr[argpos].begin(), cstr[argpos].end(), ptr);
                        ptr += cstr[argpos].size();
                    }
                }
                
                return XString::smliteraldynamic(inlined, total_size);
            }
            else {
                assert(false); // Not Implemented: full support for FString interpolation
            }
        }
    };

    inline constexpr XCString emptycstr();
    inline constexpr XString emptystr();
}

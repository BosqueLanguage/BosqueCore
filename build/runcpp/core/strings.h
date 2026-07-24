#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "postree.h"

namespace ᐸRuntimeᐳ
{
    class CStrRootInlineContent
    {
    public:
        constexpr static int64_t CSTR_BUFF_SIZE = 16;
        constexpr static int64_t CSTR_MAX_SIZE = CSTR_BUFF_SIZE - 1;

        template<size_t N>
        struct SmallLiteralInitBuffer
        {
            std::array<char, N> data;

            consteval SmallLiteralInitBuffer(const char (&cstr)[N])
            {
                static_assert(N - 1 <= CStrRootInlineContent::CSTR_MAX_SIZE, "CString literal too large for CStrRootInlineContent");
                std::copy(cstr, cstr + N, this->data.begin());
            }
        };

        std::array<char, CSTR_BUFF_SIZE> data;

        CStrRootInlineContent() : data{} { ; }
        CStrRootInlineContent(const CStrRootInlineContent& other) = default;

        bool empty() const { return static_cast<int64_t>(this->data[0]) == 0; }

        template<size_t len>
        CStrRootInlineContent(const char (&cstr)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::CStrRootInlineContent::CSTR_MAX_SIZE, "CString literal too large for CStrRootInlineContent");

            if(len == 1) {
                this->data.fill('\0');
            }
            else {
                this->data[0] = static_cast<char>(len - 1); //store length
                std::copy(cstr, cstr + len - 1, this->data.begin() + 1);
                std::fill(this->data.begin() + len, this->data.end(), '\0');
            }
        }

        template<size_t N>
        CStrRootInlineContent(SmallLiteralInitBuffer<N> slib)
        {
            static_assert(N - 1 <= ᐸRuntimeᐳ::CStrRootInlineContent::CSTR_MAX_SIZE, "CString literal too large for CStrRootInlineContent");

            if(N == 1) {
                this->data.fill('\0');
            }
            else {
                this->data[0] = static_cast<char>(N - 1); //store length
                std::copy(slib.data.begin(), slib.data.begin() + N - 1, this->data.begin() + 1);
                std::fill(this->data.begin() + N, this->data.end(), '\0');
            }
        }

        CStrRootInlineContent(const char* cstr, size_t len)
        {
            assert(len <= ᐸRuntimeᐳ::CStrRootInlineContent::CSTR_MAX_SIZE);

            this->data[0] = static_cast<char>(len); //store length
            std::copy(cstr, cstr + len, this->data.begin() + 1);
            std::fill(this->data.begin() + len + 1, this->data.end(), '\0');

        }

        int64_t size() const { return static_cast<int64_t>(this->data[0]); }
        char at(int64_t index) const { return this->data[index + 1]; }

        friend XBool operator==(const CStrRootInlineContent& lhs, const CStrRootInlineContent& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XFALSE;
            }
            else {
                return XBool::from(std::equal(lhs.data.begin() + 1, lhs.data.begin() + 1 + lhs.size(), rhs.data.begin() + 1)); 
            }
        }

        friend XBool operator<(const CStrRootInlineContent& lhs, const CStrRootInlineContent& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                auto mmpos = std::mismatch(lhs.data.begin() + 1, lhs.data.begin() + 1 + lhs.size(), rhs.data.begin() + 1);
                if(mmpos.first == lhs.data.begin() + 1 + lhs.size()) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first < *mmpos.second);
                }
            }
        }

        friend XBool operator>(const CStrRootInlineContent& lhs, const CStrRootInlineContent& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() > rhs.size());
            }
            else {
                auto mmpos = std::mismatch(lhs.data.begin() + 1, lhs.data.begin() + 1 + lhs.size(), rhs.data.begin() + 1);
                if(mmpos.first == lhs.data.begin() + 1 + lhs.size()) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first > *mmpos.second);
                } 
            } 
        }
        
        friend XBool operator!=(const CStrRootInlineContent& lhs, const CStrRootInlineContent& rhs) { return !(lhs == rhs); }
        friend XBool operator<=(const CStrRootInlineContent& lhs, const CStrRootInlineContent& rhs) { return !(lhs > rhs); }
        friend XBool operator>=(const CStrRootInlineContent& lhs, const CStrRootInlineContent& rhs) { return !(lhs < rhs); }
    };

    class CStrRootTreeContent
    {
    public:
        constexpr static int64_t CSTR_MAX_LEAF_SIZE = CStrRootInlineContent::CSTR_BUFF_SIZE * 2;
        constexpr static const char* CSTR_NODE_MASK = "00000110";

        std::array<char, 8> tags; //store tag in first byte
        PosRBTree<char, CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING> postree;

        CStrRootTreeContent() : tags{std::numeric_limits<char>::max(), 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}, postree{} { ; }
        CStrRootTreeContent(const PosRBTree<char, CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>& postree) : tags{std::numeric_limits<char>::max(), 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}, postree{postree} { ; }
        CStrRootTreeContent(const CStrRootTreeContent& other) = default;
    };

    inline constexpr TypeInfo g_typeinfo_PosRBTreeLeaf_CString = g_typeinfo_PosRBTreeLeaf_generate<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_CSTRING, BSQ_PTR_MASK_LEAF, "PosRBTreeLeaf_CString", true);
    inline constexpr TypeInfo g_typeinfo_PosRBTreeNode_CString = g_typeinfo_PosRBTreeNode_generate<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_CSTRING, CStrRootTreeContent::CSTR_NODE_MASK, "PosRBTreeNode_CString");
    inline constexpr TypeInfo g_typeinfo_PosRBTree_CString = g_typeinfo_PosRBTree_generate<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>(WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING, "PosRBTree_CString");

    extern thread_local GCAllocator<PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeLeaf_CString_allocator;
    extern thread_local GCAllocator<PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeNode_CString_allocator;

    union CStringUnion
    {
        static_assert(sizeof(CStrRootInlineContent) >= sizeof(CStrRootTreeContent));

        //empty cstring is inlinecstr, upunning type type punning for assignment and default initialization
        std::array<uint8_t, sizeof(CStrRootInlineContent)> upunning;
        CStrRootInlineContent inlinecstr;
        CStrRootTreeContent treecstr;

        CStringUnion() : upunning{} { ; }
        CStringUnion(const CStringUnion& other) = default;
        CStringUnion(const CStrRootInlineContent& c) : inlinecstr{c} { ; }
        CStringUnion(const CStrRootTreeContent& c) : treecstr{c} { ; }

        bool empty() const { return this->inlinecstr.empty(); }

        bool isInline() const { return this->inlinecstr.size() < std::numeric_limits<char>::max(); }
        bool isTree() const { return this->inlinecstr.size() == std::numeric_limits<char>::max(); }

        CStringUnion& operator=(const CStringUnion& other)
        {
            if(this == &other) {
                return *this;
            }

            this->upunning = other.upunning;
            return *this;
        }
    };

    inline constexpr TypeInfo g_typeinfo_CStringInline = {
        WELL_KNOWN_TYPE_ID_CSTRING_INLINE,
        sizeof(CStrRootInlineContent),
        byteSizeToSlotCount(sizeof(CStrRootInlineContent)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "CStringInline",
        false
    };

    inline constexpr TypeInfo g_typeinfo_CStringTree = {
        WELL_KNOWN_TYPE_ID_CSTRING_TREE,
        sizeof(CStrRootTreeContent),
        byteSizeToSlotCount(sizeof(CStrRootTreeContent)),
        LayoutTag::Value,
        "01",
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "CStringTree",
        false
    };

    inline constexpr TypeInfo g_typeinfo_CString = {
        WELL_KNOWN_TYPE_ID_CSTRING,
        sizeof(CStringUnion),
        byteSizeToSlotCount(sizeof(CStringUnion)),
        LayoutTag::Value,
        "30",
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "CString",
        false
    };

    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    class XCStringIterator
    {
    public:
        int64_t index;
        CStringUnion ucstr;

        using value_type = char;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(!this->ucstr.empty()); //should not dereference on empty string

            if(this->ucstr.isInline()) {
                return this->ucstr.inlinecstr.at(this->index);
            }
            else {
                return this->ucstr.treecstr.postree.get(this->index);
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
        CStringUnion ucstr;

    public:
        XCString() : ucstr{} { ; }
        XCString(const CStrRootInlineContent& b) : ucstr{CStringUnion{b}} { ; }
        XCString(const CStrRootTreeContent& n) : ucstr{CStringUnion{n}} { ; }
        XCString(const XCString& other) = default;

        static XCString mk(const char* cstr, size_t len)
        {
            if(len == 0) {
                return XCString{};
            }
            else {
                if(len <= CStrRootInlineContent::CSTR_MAX_SIZE) {
                    return XCString{CStrRootInlineContent(cstr, len)};
                }
                else if(len <= CStrRootTreeContent::CSTR_MAX_LEAF_SIZE) {
                    return XCString{CStrRootTreeContent{PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::mkinitial(cstr, cstr + len)}};
                }
                else {
                    return XCString{CStrRootTreeContent{PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::mklargerec(cstr, cstr + len, len)}};
                }
            }
        }

        bool empty() const
        {
            return this->ucstr.empty();
        }

        static bool gcIsTestIsInlineRepresentation(void** value)
        {
            return ((XCString*)value)->ucstr.isInline();
        }

        int64_t size() const
        {
            if(this->ucstr.isInline()) {
                return this->ucstr.inlinecstr.size();
            }
            else {
                return this->ucstr.treecstr.postree.size();
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
            if(lhs.size() != rhs.size()) {
                return XFALSE;
            }
            else {
                if(lhs.ucstr.isInline() & rhs.ucstr.isInline()) {
                    return lhs.ucstr.inlinecstr == rhs.ucstr.inlinecstr;
                }
                else {
                    return XBool::from(std::equal(lhs.begin(), lhs.end(), rhs.begin())); 
                }
            }
        }

        friend XBool operator<(const XCString& lhs, const XCString& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                if(lhs.ucstr.isInline() & rhs.ucstr.isInline()) {
                    return lhs.ucstr.inlinecstr < rhs.ucstr.inlinecstr;
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
        }

        friend XBool operator>(const XCString& lhs, const XCString& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() > rhs.size());
            }
            else {
                if(lhs.ucstr.isInline() & rhs.ucstr.isInline()) {
                    return lhs.ucstr.inlinecstr > rhs.ucstr.inlinecstr;
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
        }
        
        friend XBool operator!=(const XCString& lhs, const XCString& rhs) { return !(lhs == rhs); }
        friend XBool operator<=(const XCString& lhs, const XCString& rhs) { return !(lhs > rhs); }
        friend XBool operator>=(const XCString& lhs, const XCString& rhs) { return !(lhs < rhs); }

        static void checkFormat(XCString s, const std::basic_regex<char>& re, const char* file, uint32_t line)
        {
            if(!std::regex_match(s.begin(), s.end(), re)) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "CString does not match format"); }
        }

        static void checkSizeMin(XCString s, int64_t min, const char* file, uint32_t line)
        {
            if(s.size() < min) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "CString length below minimum"); }
        }

        static void checkSizeMax(XCString s, int64_t max, const char* file, uint32_t line)
        {
            if(max < s.size()) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "CString length above maximum"); }
        }

        static void checkSizeRange(XCString s, int64_t min, int64_t max, const char* file, uint32_t line)
        {
            if(s.size() < min) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "CString length below minimum"); }
            if(max < s.size()) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "CString length above maximum"); }
        }

        void diagnosticEmit(std::ostream& out, bool waddr) const;
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
                std::array<char, CStrRootInlineContent::CSTR_MAX_SIZE + 1> inlined = {0};
                char* ptr = inlined.data();

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
                
                return XCString::mk(inlined.data(), total_size);
            }
            else {
                assert(false); // Not Implemented: full support for FString interpolation
            }
        }
    };

    class XCRegex
    {
    public:
        size_t regexid;
    };

    class StrRootInlineContent
    {
    public:
        constexpr static int64_t STR_BUFF_SIZE = 4;
        constexpr static int64_t STR_MAX_SIZE = STR_BUFF_SIZE - 1;

        template<size_t N>
        struct SmallLiteralInitBuffer
        {
            std::array<char32_t, N> data;

            consteval SmallLiteralInitBuffer(const char32_t (&cstr)[N])
            {
                static_assert(N - 1 <= StrRootInlineContent::STR_MAX_SIZE, "String literal too large for StrRootInlineContent");
                std::copy(cstr, cstr + N, this->data.begin());
            }
        };

        std::array<char32_t, STR_BUFF_SIZE> data;

        StrRootInlineContent() : data{} { ; }
        StrRootInlineContent(const StrRootInlineContent& other) = default;

        bool empty() const { return static_cast<int64_t>(this->data[0]) == 0; }

        template<size_t len>
        StrRootInlineContent(const char32_t (&str)[len])
        {
            static_assert(len - 1 <= ᐸRuntimeᐳ::StrRootInlineContent::STR_MAX_SIZE, "String literal too large for CStrRootInlineContent");

            if(len == 1) {
                this->data.fill(U'\0');
            }
            else {
                this->data[0] = static_cast<char32_t>(len - 1); //store length
                std::copy(str, str + len - 1, this->data.begin() + 1);
                std::fill(this->data.begin() + len, this->data.end(), U'\0');
            }
        }

        template<size_t N>
        StrRootInlineContent(SmallLiteralInitBuffer<N> slib)
        {
            static_assert(N - 1 <= ᐸRuntimeᐳ::StrRootInlineContent::STR_MAX_SIZE, "String literal too large for CStrRootInlineContent");

            if(N == 1) {
                this->data.fill(U'\0');
            }
            else {
                this->data[0] = static_cast<char32_t>(N - 1); //store length
                std::copy(slib.data.begin(), slib.data.begin() + N - 1, this->data.begin() + 1);
                std::fill(this->data.begin() + N, this->data.end(), U'\0');
            }
        }

        StrRootInlineContent(const char32_t* str, size_t len)
        {
            assert(len <= ᐸRuntimeᐳ::StrRootInlineContent::STR_MAX_SIZE);

            this->data[0] = static_cast<char32_t>(len); //store length
            std::copy(str, str + len, this->data.begin() + 1);
            std::fill(this->data.begin() + len + 1, this->data.end(), U'\0');

        }

        //mask off high bits if dirty from union bit hacking
        int64_t size() const { return static_cast<int64_t>(this->data[0]); }
        char32_t at(int64_t index) const { return this->data[index + 1]; }

        friend XBool operator==(const StrRootInlineContent& lhs, const StrRootInlineContent& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XFALSE;
            }
            else {
                return XBool::from(std::equal(lhs.data.begin() + 1, lhs.data.begin() + 1 + lhs.size(), rhs.data.begin() + 1)); 
            }
        }

        friend XBool operator<(const StrRootInlineContent& lhs, const StrRootInlineContent& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                auto mmpos = std::mismatch(lhs.data.begin() + 1, lhs.data.begin() + 1 + lhs.size(), rhs.data.begin() + 1);
                if(mmpos.first == lhs.data.begin() + 1 + lhs.size()) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first < *mmpos.second);
                }
            }
        }

        friend XBool operator>(const StrRootInlineContent& lhs, const StrRootInlineContent& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() > rhs.size());
            }
            else {
                auto mmpos = std::mismatch(lhs.data.begin() + 1, lhs.data.begin() + 1 + lhs.size(), rhs.data.begin() + 1);
                if(mmpos.first == lhs.data.begin() + 1 + lhs.size()) {
                    return XBool::from(false);
                }
                else {
                    return XBool::from(*mmpos.first > *mmpos.second);
                } 
            } 
        }
        
        friend XBool operator!=(const StrRootInlineContent& lhs, const StrRootInlineContent& rhs) { return !(lhs == rhs); }
        friend XBool operator<=(const StrRootInlineContent& lhs, const StrRootInlineContent& rhs) { return !(lhs > rhs); }
        friend XBool operator>=(const StrRootInlineContent& lhs, const StrRootInlineContent& rhs) { return !(lhs < rhs); }
    };

    class StrRootTreeContent
    {
    public:
        constexpr static int64_t STR_MAX_LEAF_SIZE = StrRootInlineContent::STR_BUFF_SIZE * 2;
        constexpr static const char* STR_NODE_MASK = "00000110";

        std::array<char32_t, 2> tags; //store tag in first byte
        PosRBTree<char32_t, STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING> postree;

        StrRootTreeContent() : tags{std::numeric_limits<char32_t>::max(), 0x0}, postree{} { ; }
        StrRootTreeContent(const PosRBTree<char32_t, STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>& postree) : tags{std::numeric_limits<char32_t>::max(), 0x0}, postree{postree} { ; }
        StrRootTreeContent(const StrRootTreeContent& other) = default;
    };

    inline constexpr TypeInfo g_typeinfo_PosRBTreeLeaf_String = g_typeinfo_PosRBTreeLeaf_generate<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_STRING, BSQ_PTR_MASK_LEAF, "PosRBTreeLeaf_String", true);
    inline constexpr TypeInfo g_typeinfo_PosRBTreeNode_String = g_typeinfo_PosRBTreeNode_generate<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>(WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_STRING, StrRootTreeContent::STR_NODE_MASK, "PosRBTreeNode_String");
    inline constexpr TypeInfo g_typeinfo_PosRBTree_String = g_typeinfo_PosRBTree_generate<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>(WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING, "PosRBTree_String");

    extern thread_local GCAllocator<PosRBTreeLeaf<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeLeaf_String_allocator;
    extern thread_local GCAllocator<PosRBTreeNode<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeNode_String_allocator;

    union StringUnion
    {
        static_assert(sizeof(StrRootInlineContent) >= sizeof(StrRootTreeContent));

        //empty cstring is inlinestr, upunning type type punning for assignment and default initialization
        std::array<uint8_t, sizeof(CStrRootInlineContent)> upunning;
        StrRootInlineContent inlinestr;
        StrRootTreeContent treestr;

        StringUnion() : upunning{} { ; }
        StringUnion(const StrRootInlineContent& c) : inlinestr{c} { ; }
        StringUnion(const StrRootTreeContent& c) : treestr{c} { ; }
        StringUnion(const StringUnion& other) = default;

        bool empty() const { return this->inlinestr.empty(); }

        bool isInline() const { return this->inlinestr.size() < std::numeric_limits<char32_t>::max(); }
        bool isTree() const { return this->inlinestr.size() == std::numeric_limits<char32_t>::max(); }

        StringUnion& operator=(const StringUnion& other)
        {
            if(this == &other) {
                return *this;
            }

            this->upunning = other.upunning;
            return *this;
        }
    };

    inline constexpr TypeInfo g_typeinfo_StringInline = {
        WELL_KNOWN_TYPE_ID_STRING_INLINE,
        sizeof(StrRootInlineContent),
        byteSizeToSlotCount(sizeof(StrRootInlineContent)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "StringInline",
        false
    };

    inline constexpr TypeInfo g_typeinfo_StringTree = {
        WELL_KNOWN_TYPE_ID_STRING_TREE,
        sizeof(StrRootTreeContent),
        byteSizeToSlotCount(sizeof(StrRootTreeContent)),
        LayoutTag::Value,
        "01",
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "StringTree",
        false
    };

    inline constexpr TypeInfo g_typeinfo_String = {
        WELL_KNOWN_TYPE_ID_STRING,
        sizeof(StringUnion),
        byteSizeToSlotCount(sizeof(StringUnion)),
        LayoutTag::Value,
        "40",
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "String",
        false
    };

    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    class XStringIterator
    {
    public:
        int64_t index;
        StringUnion ustr;

        using value_type = char32_t;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(!this->ustr.empty()); //should not dereference on empty string

            if(this->ustr.isInline()) {
                return this->ustr.inlinestr.at(this->index);
            }
            else {
                return this->ustr.treestr.postree.get(this->index);
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
        StringUnion ustr;

    public:
        XString() : ustr{} { ; }
        XString(const StrRootInlineContent& b) : ustr{b} { ; }
        XString(const StrRootTreeContent& n) : ustr{n} { ; }
        XString(const XString& other) = default;

        static XString mk(const char32_t* str, size_t len)
        {
            if(len == 0) {
                return XString{};
            }
            else {
                if(len <= StrRootInlineContent::STR_MAX_SIZE) {
                    return XString{StrRootInlineContent(str, len)};
                }
                else if(len <= StrRootTreeContent::STR_MAX_LEAF_SIZE) {
                    return XString{StrRootTreeContent{PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::mkinitial(str, str + len)}};
                }
                else {
                    return XString{StrRootTreeContent{PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::mklargerec(str, str + len, len)}};
                }
            }
        }

        bool empty() const
        {
            return this->ustr.empty();
        }

        static bool gcIsTestIsInlineRepresentation(void** value)
        {
            return ((XString*)value)->ustr.isInline();
        }

        int64_t size() const
        {
            if(this->ustr.isInline()) {
                return this->ustr.inlinestr.size();
            }
            else {
                return this->ustr.treestr.postree.size();
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
            if(lhs.size() != rhs.size()) {
                return XFALSE;
            }
            else {
                if(lhs.ustr.isInline() & rhs.ustr.isInline()) {
                    return lhs.ustr.inlinestr == rhs.ustr.inlinestr;
                }
                else {
                    return XBool::from(std::equal(lhs.begin(), lhs.end(), rhs.begin()));
                }
            }
        }

        friend XBool operator<(const XString& lhs, const XString& rhs) 
        {
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() < rhs.size());
            }
            else {
                if(lhs.ustr.isInline() & rhs.ustr.isInline()) {
                    return lhs.ustr.inlinestr < rhs.ustr.inlinestr;
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
        }

        friend XBool operator>(const XString& lhs, const XString& rhs) 
        { 
            if(lhs.size() != rhs.size()) {
                return XBool::from(lhs.size() > rhs.size());
            }
            else {
                if(lhs.ustr.isInline() & rhs.ustr.isInline()) {
                    return lhs.ustr.inlinestr > rhs.ustr.inlinestr;
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
        }
        
        friend XBool operator!=(const XString& lhs, const XString& rhs) { return !(lhs == rhs); }
        friend XBool operator<=(const XString& lhs, const XString& rhs) { return !(lhs > rhs); }
        friend XBool operator>=(const XString& lhs, const XString& rhs) { return !(lhs < rhs); }

        static void checkFormat(XString s, const std::basic_regex<char32_t>& re, const char* file, uint32_t line)
        {
            if(!std::regex_match(s.begin(), s.end(), re)) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "String does not match format"); }
        }

        static void checkSizeMin(XString s, int64_t min, const char* file, uint32_t line)
        {
            if(s.size() < min) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "String length below minimum"); }
        }

        static void checkSizeMax(XString s, int64_t max, const char* file, uint32_t line)
        {
            if(max < s.size()) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "String length above maximum"); }
        }

        static void checkSizeRange(XString s, int64_t min, int64_t max, const char* file, uint32_t line)
        {
            if(s.size() < min) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "String length below minimum"); }
            if(max < s.size()) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::UserInvariant, nullptr, "String length above maximum"); }
        }

        void diagnosticEmit(std::ostream& out, bool waddr) const;
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
                std::array<char32_t, StrRootInlineContent::STR_MAX_SIZE + 1> inlined = {0};
                char32_t* ptr = inlined.data();

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
                
                return XString::mk(inlined.data(), total_size);
            }
            else {
                assert(false); // Not Implemented: full support for FString interpolation
            }
        }
    };

    class XRegex
    {
    public:
        size_t regexid;
    };
}

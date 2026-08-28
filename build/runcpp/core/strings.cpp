#include "strings.h"

namespace ᐸRuntimeᐳ
{
    thread_local GCAllocator<PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeLeaf_CString_allocator(&g_typeinfo_PosRBTreeLeaf_CString);
    thread_local GCAllocator<PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeNode_CString_allocator(&g_typeinfo_PosRBTreeNode_CString);

    template<> const TypeInfo* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::s_leaftypeinfo = &g_typeinfo_PosRBTreeLeaf_CString;
    template<> thread_local GCAllocator<PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>>* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::s_leafallocator = &PosRBTreeLeaf_CString_allocator;
    template<> const TypeInfo* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::s_nodetypeinfo = &g_typeinfo_PosRBTreeNode_CString;
    template<> thread_local GCAllocator<PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>>* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::s_nodeallocator = &PosRBTreeNode_CString_allocator;

    thread_local GCAllocator<PosRBTreeLeaf<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeLeaf_String_allocator(&g_typeinfo_PosRBTreeLeaf_String);
    thread_local GCAllocator<PosRBTreeNode<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeNode_String_allocator(&g_typeinfo_PosRBTreeNode_String);

    template<> const TypeInfo* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::s_leaftypeinfo = &g_typeinfo_PosRBTreeLeaf_String;
    template<> thread_local GCAllocator<PosRBTreeLeaf<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>>* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::s_leafallocator = &PosRBTreeLeaf_String_allocator;
    template<> const TypeInfo* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::s_nodetypeinfo = &g_typeinfo_PosRBTreeNode_String;
    template<> thread_local GCAllocator<PosRBTreeNode<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>>* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::s_nodeallocator = &PosRBTreeNode_String_allocator;

    void XCString::diagnosticEmit(std::ostream& out, bool waddr) const
    {
        if(this->ucstr.isInline()) {
            out << "'";
            for(int64_t i = 0; i < this->ucstr.inlinecstr.data[0]; i++) {
                out << this->ucstr.inlinecstr.data[i + 1];
            }
            out << "'";
        }
        else {
            assert(false); // Not Implemented: diagnostic emit for non-inline strings
        }
    }

    XCString XCString::natToCString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llin", (long long int)value);
        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::intToCString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llii", (long long int)value);
        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::chkNatToCString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliN", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkNat values
        }

        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::chkIntToCString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliI", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkInt values
        }

        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::floatToCString(double value) {
        char numbuf[64];
        int written = 0;
        
        if(std::floor(value) != value) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lgf", value);
        }
        else {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lg.0f", value);
        }

        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XByteBuffer XCString::toByteBuffer(const XCString& cstr)
    {
        if(cstr.empty()) {
            return XByteBuffer{};
        }
        else {
            //TODO: this is not the best in terms of memory/compute but is simple for now
            std::vector<uint8_t> buffer{};
            buffer.reserve(cstr.size());
            std::transform(cstr.begin(), cstr.end(), std::back_inserter(buffer), [](uint8_t b) { return static_cast<uint8_t>(b); });

            return XByteBuffer::mk(buffer.data(), buffer.data() + buffer.size(), buffer.size());
        }
    }

    XBool XCString::fromByteBuffer(const XByteBuffer& buffer, XCString& result)
    {
        if(buffer.bytes() == 0) {
            result = XCString{};
            return XTRUE;
        }
        else {
            //TODO: this is not the best in terms of memory/compute but is simple for now
            
            if(buffer.isInline()) {
                bool allok = std::all_of(buffer.inlinedata(), buffer.inlinedata() + buffer.bytes(), [](uint8_t b) { return isLegalCChar(b); });
                if(!allok) {
                    return XFALSE;
                }
                else {
                    std::vector<char> cbb{};
                    cbb.reserve(buffer.bytes());
                    std::transform(buffer.inlinedata(), buffer.inlinedata() + buffer.bytes(), std::back_inserter(cbb), [](uint8_t b) { return static_cast<char>(b); });
                    
                    result = XCString::mk(cbb.begin(), cbb.end(),  cbb.size());
                    return XTRUE;
                }
            }
            else {
                bool allok = std::all_of(buffer.begin(), buffer.end(), [](uint8_t b) { return isLegalCChar(b); });
                if(!allok) {
                    return XFALSE;
                }
                else {
                    std::vector<char> cbb{};
                    cbb.reserve(buffer.bytes());
                    std::transform(buffer.begin(), buffer.end(), std::back_inserter(cbb), [](uint8_t b) { return static_cast<char>(b); });
                    
                    result = XCString::mk(cbb.begin(), cbb.end(),  cbb.size());
                    return XTRUE;
                }
            }
        }
    }

    XCString XCString::append(XCString other)
    {
        assert(!this->ucstr.empty());
        assert(!other.ucstr.empty());

        if(this->ucstr.isInline() && other.ucstr.isInline()) {
            if(this->ucstr.inlinecstr.data[0] + other.ucstr.inlinecstr.data[0] <= CStrRootInlineContent::CSTR_MAX_SIZE) {
                return XCString{CStrRootInlineContent{this->ucstr.inlinecstr, other.ucstr.inlinecstr}};
            }
            else {
                static_assert(CStrRootInlineContent::CSTR_MAX_SIZE * 2 <= CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, "If this changes then we need more complex logic like in list append");
                
                return XCString{CStrRootTreeContent{PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::mkinitial_append(this->ucstr.inlinecstr.data.begin() + 1, this->ucstr.inlinecstr.data.begin() + 1 + this->ucstr.inlinecstr.data[0], other.ucstr.inlinecstr.data.begin() + 1, other.ucstr.inlinecstr.data.begin() + 1 + other.ucstr.inlinecstr.data[0])}};
            }
        }
        else {
            PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING> lnode{};
            if(this->ucstr.isInline()) {
                lnode = PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::mkinitial(this->ucstr.inlinecstr.data.begin() + 1, this->ucstr.inlinecstr.data.begin() + 1 + this->ucstr.inlinecstr.data[0]);
            }
            else {
                lnode = this->ucstr.treecstr.postree;
            }

            PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING> rnode{};
            if(other.ucstr.isInline()) {
                rnode = PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::mkinitial(other.ucstr.inlinecstr.data.begin() + 1, other.ucstr.inlinecstr.data.begin() + 1 + other.ucstr.inlinecstr.data[0]);
            }
            else {
                rnode = other.ucstr.treecstr.postree;
            }

            return XCString{CStrRootTreeContent{PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING>::append(lnode, rnode)}};
        }
    }

    void XString::diagnosticEmit(std::ostream& out, bool waddr) const
    {
        if(this->ustr.isInline()) {
            out << "\"";
            for(int64_t i = 0; i < this->ustr.inlinestr.data[0]; i++) {
                out << (char)this->ustr.inlinestr.data[i + 1];
            }
            out << "\"";
        }
        else {
            assert(false); // Not Implemented: diagnostic emit for non-inline strings
        }
    }

    XString XString::natToString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llin", (long long int)value);

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::intToString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llii", (long long int)value);

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::chkNatToString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliN", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkNat values
        }

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::chkIntToString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliI", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkInt values
        }

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::floatToString(double value) {
        char numbuf[64];
        int written = 0;
        
        if(std::floor(value) != value) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lgf", value);
        }
        else {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lg.0f", value);
        }

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::fromCString(const XCString& cstr)
    {
        if(cstr.empty()) {
            return XString{};
        }
        else {
            //TODO: this is not the best in terms of memory/compute but is simple for now
            std::vector<char32_t> buffer{};
            buffer.reserve(cstr.size());
            std::transform(cstr.begin(), cstr.end(), std::back_inserter(buffer), [](char c) { return static_cast<char32_t>(c); });

            return XString::mk(buffer.begin(), buffer.end(), buffer.size());
        }
    }

    XBool XString::toCString(const XString& str, XCString& cstr)
    {
        if(str.empty()) {
            cstr = XCString{};
            return XTRUE;
        }
        else {
            //TODO: this is not the best in terms of memory/compute but is simple for now
            bool allok = std::all_of(str.begin(), str.end(), [](char32_t c) { return c <= 0x7F && isLegalCChar(static_cast<uint8_t>(c)); });
            
            if(!allok) {
                return XFALSE;
            }
            else {
                std::vector<char> cbb{};
                cbb.reserve(str.size());
                std::transform(str.begin(), str.end(), std::back_inserter(cbb), [](char32_t c) { return static_cast<char>(c); });
                    
                cstr = XCString::mk(cbb.begin(), cbb.end(),  cbb.size());
                return XTRUE;
            }
        }
    }

    XByteBuffer XString::toByteBuffer(const XString& str)
    {
        if(str.empty()) {
            return XByteBuffer{};
        }
        else {
            //TODO: this is not the best in terms of memory/compute but is simple for now
            std::vector<uint8_t> buffer{};
            buffer.reserve(str.size());

            std::array<uint8_t, 4> outbuff{};
            for(auto ii = str.begin(); ii != str.end(); ++ii) {
                char32_t cc = *ii;
                if(cc <= 0x7F) {
                    buffer.push_back(static_cast<uint8_t>(cc));
                }
                else {
                    size_t count = ucharToMultiByteEncoding(cc, outbuff);
                    buffer.insert(buffer.end(), outbuff.begin(), outbuff.begin() + count);
                }
            }

            return XByteBuffer::mk(buffer.data(), buffer.data() + buffer.size(), buffer.size());
        }
    }

    XBool XString::fromByteBuffer(const XByteBuffer& buffer, XString& result)
    {
        if(buffer.bytes() == 0) {
            result = XString{};
            return XTRUE;
        }
        else {
            //TODO: this is not the best in terms of memory/compute but is simple for now
            std::vector<char32_t> cbb{};
            cbb.reserve(buffer.bytes());

            if(buffer.isInline()) {
                size_t ii = 0;
                const uint8_t* inlinedata = buffer.inlinedata();
                while(ii < buffer.bytes()) {
                    uint8_t cc = inlinedata[ii];

                    if(!isMultibyteEncoding(cc)) {
                        cbb.push_back(static_cast<char32_t>(cc));
                        ii++;
                    }
                    else {
                        size_t mbcc = multibyteCharCount(cc);
                        if(mbcc == 0 || buffer.bytes() < ii + mbcc)
                        {
                            return XFALSE;
                        }

                        std::array<uint8_t, 4> inbuff{};
                        std::copy(inlinedata + ii, inlinedata + ii + mbcc, inbuff.begin());

                        char32_t cc = multibyteToUChar(inbuff, mbcc);
                        if(!isLegalUnicodeChar(cc)) {
                            return XFALSE;
                        }

                        cbb.push_back(cc);
                        ii += mbcc;
                    }
                }
                    
                result = XString::mk(cbb.begin(), cbb.end(),  cbb.size());
                return XTRUE;
            }
            else {
                auto ii = buffer.begin();
                while(ii != buffer.end()) {
                    uint8_t cc = *ii;

                    if(!isMultibyteEncoding(cc)) {
                        cbb.push_back(static_cast<char32_t>(cc));
                        ii++;
                    }
                    else {
                        size_t mbcc = multibyteCharCount(cc);
                        if(mbcc == 0 || ii.totalbytes < ii.gindex + mbcc) {
                            return XFALSE;
                        }

                        std::array<uint8_t, 4> inbuff{};
                        for(size_t j = 0; j < mbcc; j++) {
                            inbuff[j] = *ii;
                            ++ii;
                        }

                        char32_t cc = multibyteToUChar(inbuff, mbcc);
                        if(!isLegalUnicodeChar(cc)) {
                            return XFALSE;
                        }

                        cbb.push_back(cc);
                        //ii is advanced during copyt
                    }
                }

                result = XString::mk(cbb.begin(), cbb.end(),  cbb.size());
                return XTRUE;
            }
        }
    }

    XString XString::append(XString other)
    {
        assert(!this->ustr.empty());
        assert(!other.ustr.empty());

        if(this->ustr.isInline() && other.ustr.isInline()) {
            if(this->ustr.inlinestr.data[0] + other.ustr.inlinestr.data[0] <= StrRootInlineContent::STR_MAX_SIZE) {
                return XString{StrRootInlineContent{this->ustr.inlinestr, other.ustr.inlinestr}};
            }
            else {
                static_assert(StrRootInlineContent::STR_MAX_SIZE * 2 <= StrRootTreeContent::STR_MAX_LEAF_SIZE, "If this changes then we need more complex logic like in list append");
                
                return XString{StrRootTreeContent{PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::mkinitial_append(this->ustr.inlinestr.data.begin() + 1, this->ustr.inlinestr.data.begin() + 1 + this->ustr.inlinestr.data[0], other.ustr.inlinestr.data.begin() + 1, other.ustr.inlinestr.data.begin() + 1 + other.ustr.inlinestr.data[0])}};
            }
        }
        else {
            PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING> lnode{};
            if(this->ustr.isInline()) {
                lnode = PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::mkinitial(this->ustr.inlinestr.data.begin() + 1, this->ustr.inlinestr.data.begin() + 1 + this->ustr.inlinestr.data[0]);
            }
            else {
                lnode = this->ustr.treestr.postree;
            }

            PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING> rnode{};
            if(other.ustr.isInline()) {
                rnode = PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::mkinitial(other.ustr.inlinestr.data.begin() + 1, other.ustr.inlinestr.data.begin() + 1 + other.ustr.inlinestr.data[0]);
            }
            else {
                rnode = other.ustr.treestr.postree;
            }

            return XString{StrRootTreeContent{PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING>::append(lnode, rnode)}};
        }
    }
}

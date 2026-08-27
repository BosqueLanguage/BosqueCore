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

    XByteBuffer XCString::cstrToByteBuffer(const XCString& cstr)
    {
        return XByteBuffer::mk(cstr.begin(), cstr.end(), cstr.size());
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
                    result = XCString::mk(buffer.inlinedata(), buffer.inlinedata() + buffer.bytes(),  buffer.bytes());
                    return XTRUE;
                }
            }
            else {
                bool allok = std::all_of(buffer.begin(), buffer.end(), [](uint8_t b) { return isLegalCChar(b); });
                if(!allok) {
                    return XFALSE;
                }
                else {
                    result = XCString::mk(buffer.begin(), buffer.end(),  buffer.bytes());
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

    XString XString::append(XString other)
    {
        assert(false); // Not Implemented: append for XString
    }
}

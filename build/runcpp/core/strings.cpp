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
        }
        else {
            assert(false); // Not Implemented: diagnostic emit for non-inline strings
        }
    }

    void XString::diagnosticEmit(std::ostream& out, bool waddr) const
    {
        if(this->ustr.isInline()) {
            out << "'";
            for(int64_t i = 0; i < this->ustr.inlinestr.data[0]; i++) {
                out << (char)this->ustr.inlinestr.data[i + 1];
            }
        }
        else {
            assert(false); // Not Implemented: diagnostic emit for non-inline strings
        }
    }
}

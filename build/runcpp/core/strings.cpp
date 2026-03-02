#include "strings.h"

namespace ᐸRuntimeᐳ
{
    template<> const TypeInfo* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>::bbleaftype = &g_typeinfo_PosRBTreeLeafEmpty_CString;
    template<> const TypeInfo* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>::leaftype = &g_typeinfo_PosRBTreeLeaf_CString;
    template<> const TypeInfo* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>::nodetype = &g_typeinfo_PosRBTreeNode_CString;

    template<> const TypeInfo* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>::bbleaftype = &g_typeinfo_PosRBTreeLeafEmpty_String;
    template<> const TypeInfo* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>::leaftype = &g_typeinfo_PosRBTreeLeaf_String;
    template<> const TypeInfo* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>::nodetype = &g_typeinfo_PosRBTreeNode_String;
}

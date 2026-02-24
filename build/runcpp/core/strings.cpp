#include "strings.h"

namespace ᐸRuntimeᐳ
{
    template<> uint32_t PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>::bbleaftypeid = g_typeinfo_PosRBTreeLeafEmpty_CString.bsqtypeid;
    template<> uint32_t PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>::leaftypeid = g_typeinfo_PosRBTreeLeaf_CString.bsqtypeid;
    template<> uint32_t PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>::nodetypeid = g_typeinfo_PosRBTreeNode_CString.bsqtypeid;
}

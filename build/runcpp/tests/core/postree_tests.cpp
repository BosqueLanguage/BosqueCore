#include <boost/test/unit_test.hpp>

#include "../../core/postree.h"

#define BSQ_POSTREE_ID 12
#define BSQ_POSTREE_NODE_ID (BSQ_POSTREE_ID - 1)
#define BSQ_POSTREE_LEAF_ID (BSQ_POSTREE_NODE_ID - 1)

using PTreeInt4 = ᐸRuntimeᐳ::PosRBTree<int64_t, 4, BSQ_POSTREE_ID>;

const ᐸRuntimeᐳ::TypeInfo PTreeInt4_leaftypeinfo = ᐸRuntimeᐳ::g_typeinfo_PosRBTreeLeaf_generate<int64_t, 4>(BSQ_POSTREE_LEAF_ID, BSQ_PTR_MASK_LEAF, "PosRBTreeLeaf_Int64");
template<> const ᐸRuntimeᐳ::TypeInfo* PTreeInt4::s_leaftypeinfo = &PTreeInt4_leaftypeinfo;
thread_local ᐸRuntimeᐳ::GCAllocator<ᐸRuntimeᐳ::PosRBTreeLeaf<int64_t, 4>> PTreeInt4_leafallocator(&PTreeInt4_leaftypeinfo);
template<> thread_local ᐸRuntimeᐳ::GCAllocator<ᐸRuntimeᐳ::PosRBTreeLeaf<int64_t, 4>>* PTreeInt4::s_leafallocator = &PTreeInt4_leafallocator;

const ᐸRuntimeᐳ::TypeInfo PTreeInt4_nodetypeinfo = ᐸRuntimeᐳ::g_typeinfo_PosRBTreeNode_generate<int64_t, 4>(BSQ_POSTREE_NODE_ID, "000000110", "PosRBTreeNode_Int64");
template<> const ᐸRuntimeᐳ::TypeInfo* PTreeInt4::s_nodetypeinfo = &PTreeInt4_nodetypeinfo;
thread_local ᐸRuntimeᐳ::GCAllocator<ᐸRuntimeᐳ::PosRBTreeNode<int64_t, 4>> PTreeInt4_nodeallocator(&PTreeInt4_nodetypeinfo);
template<> thread_local ᐸRuntimeᐳ::GCAllocator<ᐸRuntimeᐳ::PosRBTreeNode<int64_t, 4>>* PTreeInt4::s_nodeallocator = &PTreeInt4_nodeallocator;

BOOST_AUTO_TEST_SUITE(PosTreeTests)

BOOST_AUTO_TEST_SUITE(Basics)

BOOST_AUTO_TEST_CASE(MakeLeaf_PushBack) {
    static_assert(sizeof(ᐸRuntimeᐳ::PosRBData<int64_t, 4>) == 40);
    static_assert(sizeof(ᐸRuntimeᐳ::PosRBTreeLeaf<int64_t, 4>) == 40);
    static_assert(sizeof(ᐸRuntimeᐳ::PosRBTreeNode<int64_t, 4>) == 64);
    static_assert(sizeof(ᐸRuntimeᐳ::PosRBTree<int64_t, 4, BSQ_POSTREE_ID>) == 8);

    PTreeInt4 tree{PTreeInt4::s_leafallocator->construct(ᐸRuntimeᐳ::PosRBData<int64_t, 4>(ᐸRuntimeᐳ::RColor::Black, 2, 0))};
    for(int i = 0; i < 20; i++) {
        tree = tree.pushBack(i);
    }

    PTreeInt4_leafallocator.cleanup();
    PTreeInt4_nodeallocator.cleanup();
}

BOOST_AUTO_TEST_SUITE_END() //Basics


BOOST_AUTO_TEST_SUITE_END() //PosTreeTests

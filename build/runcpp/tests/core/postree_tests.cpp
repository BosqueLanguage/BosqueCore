#include <boost/test/unit_test.hpp>

#include "../../core/postree.h"

#define BSQ_POSTREE_ID 12
#define BSQ_POSTREE_NODE_ID (BSQ_POSTREE_ID - 1)
#define BSQ_POSTREE_LEAF_ID (BSQ_POSTREE_NODE_ID - 1)

BOOST_AUTO_TEST_SUITE(PosTreeTests)

BOOST_AUTO_TEST_SUITE(Basics)

BOOST_AUTO_TEST_CASE(MakeLeaf_PushBack) {
    using PTree = ᐸRuntimeᐳ::PosRBTree<int64_t, 4, BSQ_POSTREE_ID>;

    auto leaftypeinfo = ᐸRuntimeᐳ::g_typeinfo_PosRBTreeLeaf_generate<int64_t, 4>(BSQ_POSTREE_LEAF_ID, BSQ_PTR_MASK_LEAF, "PosRBTreeLeaf_Int64");
    auto leafallocator = ᐸRuntimeᐳ::GCAllocator<ᐸRuntimeᐳ::PosRBTreeLeaf<int64_t, 4>>(&leaftypeinfo);

    PTree::s_leaftypeinfo = &leaftypeinfo;
    PTree::s_leafallocator = &leafallocator;

    auto nodetypeinfo = ᐸRuntimeᐳ::g_typeinfo_PosRBTreeNode_generate<int64_t, 4>(BSQ_POSTREE_NODE_ID, "000000110", "PosRBTreeNode_Int64");
    auto nodeallocator = ᐸRuntimeᐳ::GCAllocator<ᐸRuntimeᐳ::PosRBTreeNode<int64_t, 4>>(&nodetypeinfo);

    PTree::s_nodetypeinfo = &nodetypeinfo;
    PTree::s_nodeallocator = &nodeallocator;

    PTree tree{PTree::s_leafallocator->allocate(ᐸRuntimeᐳ::RColor::Black, ᐸRuntimeᐳ::PosRBData<int64_t, 4>(ᐸRuntimeᐳ::RColor::Black, 1, 0))};
    for(int i = 0; i < 10; i++) {
        tree = tree.pushBack(i);
    }

    leafallocator.cleanup();
    nodeallocator.cleanup();
}

BOOST_AUTO_TEST_SUITE_END() //Basics


BOOST_AUTO_TEST_SUITE_END() //PosTreeTests

#define BOOST_TEST_MODULE postree_tests
#include <boost/test/included/unit_test.hpp>

#include "../core/postree.h"

#include <random>
#include <vector>

namespace ᐸRuntimeᐳ
{
    constexpr uint32_t TEST_POSTREE_LEAF_TID = 1001;
    constexpr uint32_t TEST_POSTREE_NODE_TID = 1002;
    constexpr uint32_t TEST_POSTREE_TREE_TID = 1003;
    constexpr int64_t TEST_POSTREE_LEAF_SIZE = 6;

    inline constexpr auto g_typeinfo_PosRBTreeLeaf_TestInt = g_typeinfo_PosRBTreeLeaf_generate<int, TEST_POSTREE_LEAF_SIZE>(TEST_POSTREE_LEAF_TID, BSQ_TYPEINFO_NO_ESLOT, nullptr, "TestPosRBTreeLeaf");
    inline constexpr auto g_typeinfo_PosRBTreeNode_TestInt = g_typeinfo_PosRBTreeNode_generate<int, TEST_POSTREE_LEAF_SIZE>(TEST_POSTREE_NODE_TID, "TestPosRBTreeNode");

    thread_local GCAllocator<PosRBTreeLeaf<int, TEST_POSTREE_LEAF_SIZE>> g_test_postree_leaf_allocator(&g_typeinfo_PosRBTreeLeaf_TestInt);
    thread_local GCAllocator<PosRBTreeNode<int, TEST_POSTREE_LEAF_SIZE>> g_test_postree_node_allocator(&g_typeinfo_PosRBTreeNode_TestInt);

    template<> const TypeInfo* PosRBTree<int, TEST_POSTREE_LEAF_SIZE, TEST_POSTREE_TREE_TID>::s_leaftypeinfo = &g_typeinfo_PosRBTreeLeaf_TestInt;
    template<> thread_local GCAllocator<PosRBTreeLeaf<int, TEST_POSTREE_LEAF_SIZE>>* PosRBTree<int, TEST_POSTREE_LEAF_SIZE, TEST_POSTREE_TREE_TID>::s_leafallocator = &g_test_postree_leaf_allocator;
    template<> const TypeInfo* PosRBTree<int, TEST_POSTREE_LEAF_SIZE, TEST_POSTREE_TREE_TID>::s_nodetypeinfo = &g_typeinfo_PosRBTreeNode_TestInt;
    template<> thread_local GCAllocator<PosRBTreeNode<int, TEST_POSTREE_LEAF_SIZE>>* PosRBTree<int, TEST_POSTREE_LEAF_SIZE, TEST_POSTREE_TREE_TID>::s_nodeallocator = &g_test_postree_node_allocator;
}

using TestTree = ᐸRuntimeᐳ::PosRBTree<int, ᐸRuntimeᐳ::TEST_POSTREE_LEAF_SIZE, ᐸRuntimeᐳ::TEST_POSTREE_TREE_TID>;

struct AllocatorCleanupFixture
{
    ~AllocatorCleanupFixture()
    {
        ᐸRuntimeᐳ::g_test_postree_leaf_allocator.cleanup();
        ᐸRuntimeᐳ::g_test_postree_node_allocator.cleanup();
    }
};

static TestTree make_singleton_tree(int value)
{
    return TestTree::mkwleaf(TestTree::s_leafallocator->allocate(&value, &value + 1));
}

static TestTree build_tree(const std::vector<int>& values)
{
    if(values.empty()) {
        return TestTree{};
    }

    TestTree tree = make_singleton_tree(values[0]);
    for(size_t i = 1; i < values.size(); ++i) {
        tree = tree.insert(i, values[i]);
    }

    return tree;
}

static TestTree insert_value(const TestTree& tree, int64_t index, int value)
{
    if(tree.count() == 0) {
        BOOST_REQUIRE_EQUAL(index, 0);
        return make_singleton_tree(value);
    }

    return tree.insert(index, value);
}

static std::vector<int> snapshot_tree(const TestTree& tree)
{
    std::vector<int> values;
    values.reserve(tree.count());

    for(int64_t i = 0; i < tree.count(); ++i) {
        values.push_back(tree.get(i));
    }

    return values;
}

static void check_tree_matches(const TestTree& tree, const std::vector<int>& expected)
{
    BOOST_REQUIRE(TestTree::checkRBInvariants(tree));
    BOOST_REQUIRE(TestTree::checkCountInvariant(tree.repr));
    BOOST_REQUIRE_EQUAL(tree.count(), static_cast<int64_t>(expected.size()));

    const std::vector<int> actual = snapshot_tree(tree);
    BOOST_TEST(actual == expected, boost::test_tools::per_element());
}

static void check_tree_matches_periodic(const TestTree& tree, const std::vector<int>& expected, size_t step, size_t interval)
{
    if(step % interval == 0 || step + 1 == expected.size() || expected.empty()) {
        check_tree_matches(tree, expected);
    }
}

BOOST_FIXTURE_TEST_CASE(remove_from_single_leaf_keeps_sequence, AllocatorCleanupFixture)
{
    const std::vector<int> seed = {1, 2, 3, 4, 5, 6};
    for(size_t i = 0; i < seed.size(); ++i) {
        TestTree tree = build_tree(seed);
        std::vector<int> expected = seed;
        expected.erase(expected.begin() + i);

        tree = tree.remove(i);
        check_tree_matches(tree, expected);
    }
}

BOOST_FIXTURE_TEST_CASE(remove_single_element_tree_to_empty, AllocatorCleanupFixture)
{
    TestTree tree = make_singleton_tree(42);
    tree = tree.remove(0);

    check_tree_matches(tree, {});
}

BOOST_FIXTURE_TEST_CASE(remove_every_index_from_deeper_tree, AllocatorCleanupFixture)
{
    for(int size = 7; size <= 48; ++size) {
        std::vector<int> seed(size);
        for(int i = 0; i < size; ++i) {
            seed[i] = i * 3;
        }

        for(int index = 0; index < size; ++index) {
            TestTree tree = build_tree(seed);
            std::vector<int> expected = seed;
            expected.erase(expected.begin() + index);

            tree = tree.remove(index);
            check_tree_matches(tree, expected);
        }
    }
}

BOOST_FIXTURE_TEST_CASE(repeated_remove_front_to_empty, AllocatorCleanupFixture)
{
    for(int size = 1; size <= 48; ++size) {
        std::vector<int> expected(size);
        for(int i = 0; i < size; ++i) {
            expected[i] = i;
        }

        TestTree tree = build_tree(expected);
        while(!expected.empty()) {
            tree = tree.remove(0);
            expected.erase(expected.begin());
            check_tree_matches(tree, expected);
        }
    }
}

BOOST_FIXTURE_TEST_CASE(repeated_remove_back_to_empty, AllocatorCleanupFixture)
{
    for(int size = 1; size <= 48; ++size) {
        std::vector<int> expected(size);
        for(int i = 0; i < size; ++i) {
            expected[i] = i;
        }

        TestTree tree = build_tree(expected);
        while(!expected.empty()) {
            tree = tree.remove(expected.size() - 1);
            expected.pop_back();
            check_tree_matches(tree, expected);
        }
    }
}

BOOST_FIXTURE_TEST_CASE(mixed_insert_remove_matches_vector_model, AllocatorCleanupFixture)
{
    TestTree tree = build_tree({10, 20, 30, 40, 50, 60, 70, 80});
    std::vector<int> expected = {10, 20, 30, 40, 50, 60, 70, 80};
    int next_value = 1000;

    for(int step = 0; step < 160; ++step) {
        const bool do_insert = expected.empty() || (step % 5 == 0) || (step % 7 == 0);
        if(do_insert) {
            const int64_t index = (step * 11) % (expected.size() + 1);
            tree = insert_value(tree, index, next_value);
            expected.insert(expected.begin() + index, next_value);
            ++next_value;
        }
        else {
            const int64_t index = (step * 13) % expected.size();
            tree = tree.remove(index);
            expected.erase(expected.begin() + index);
        }

        check_tree_matches(tree, expected);
    }
}

BOOST_FIXTURE_TEST_CASE(large_sequential_append_then_remove_front, AllocatorCleanupFixture)
{
    constexpr size_t check_interval = 25;
    for(const int size : {500, 750, 1000}) {
        TestTree tree;
        std::vector<int> expected;
        expected.reserve(size);

        for(int value = 0; value < size; ++value) {
            tree = insert_value(tree, expected.size(), value * 2);
            expected.push_back(value * 2);
            check_tree_matches_periodic(tree, expected, expected.size() - 1, check_interval);
        }

        check_tree_matches(tree, expected);

        for(int removed = 0; removed < size; ++removed) {
            tree = tree.remove(0);
            expected.erase(expected.begin());
            check_tree_matches_periodic(tree, expected, removed, check_interval);
        }

        check_tree_matches(tree, expected);
    }
}

BOOST_FIXTURE_TEST_CASE(large_sequential_prepend_then_remove_back, AllocatorCleanupFixture)
{
    constexpr size_t check_interval = 25;
    for(const int size : {500, 750, 1000}) {
        TestTree tree;
        std::vector<int> expected;
        expected.reserve(size);

        for(int value = 0; value < size; ++value) {
            tree = insert_value(tree, 0, value + 10000);
            expected.insert(expected.begin(), value + 10000);
            check_tree_matches_periodic(tree, expected, value, check_interval);
        }

        check_tree_matches(tree, expected);

        for(int removed = 0; removed < size; ++removed) {
            tree = tree.remove(expected.size() - 1);
            expected.pop_back();
            check_tree_matches_periodic(tree, expected, removed, check_interval);
        }

        check_tree_matches(tree, expected);
    }
}

BOOST_FIXTURE_TEST_CASE(seed_random_large_insert_delete_matches_vector_model, AllocatorCleanupFixture)
{
    constexpr size_t min_size = 500;
    constexpr size_t max_size = 1000;
    constexpr int steps = 3000;

    for(const uint32_t seed : {0x00C0FFEEu, 0x5EED1234u, 0x12345678u}) {
        std::mt19937 rng(seed);

        TestTree tree;
        std::vector<int> expected;
        expected.reserve(max_size + steps);

        int next_value = static_cast<int>(seed);
        for(size_t i = 0; i < min_size; ++i) {
            const int64_t index = expected.empty() ? 0 : static_cast<int64_t>(rng() % (expected.size() + 1));
            tree = insert_value(tree, index, next_value++);
            expected.insert(expected.begin() + index, next_value - 1);
        }

        check_tree_matches(tree, expected);

        for(int step = 0; step < steps; ++step) {
            const bool must_insert = expected.size() < min_size;
            const bool must_delete = expected.size() > max_size;
            const bool do_insert = must_insert || (!must_delete && ((rng() & 1u) == 0u));

            if(do_insert) {
                const int64_t index = static_cast<int64_t>(rng() % (expected.size() + 1));
                tree = insert_value(tree, index, next_value++);
                expected.insert(expected.begin() + index, next_value - 1);
            }
            else {
                const int64_t index = static_cast<int64_t>(rng() % expected.size());
                tree = tree.remove(index);
                expected.erase(expected.begin() + index);
            }

            check_tree_matches(tree, expected);
        }
    }
}

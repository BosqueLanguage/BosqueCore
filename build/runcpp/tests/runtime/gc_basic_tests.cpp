#define BOOST_TEST_MODULE CoreTests_GC_Basics
#include <boost/test/included/unit_test.hpp>

#include "../../common.h"
#include "../../runtime/allocator/gc.h"
#include "../../core/coredecls.h"

//Primitive decls
using None = ᐸRuntimeᐳ::XNone;
using Bool = ᐸRuntimeᐳ::XBool;
using Int = ᐸRuntimeᐳ::XInt;


class MainᕒLeaf {
public:
    Int a;    
    Int b;    
    Int c;    
    Int d;    
    Int e;
    //All constructor and assignment defaults
};
namespace ᐸRuntimeᐳ {
    inline constexpr FieldOffsetInfo g_ftable_MainᕒLeaf[5] = {
        { 0, 2, 0, 0, "Main::Leaf--a", "a" },
        { 1, 2, 8, 1, "Main::Leaf--b", "b" },
        { 2, 2, 16, 2, "Main::Leaf--c", "c" },
        { 3, 2, 24, 3, "Main::Leaf--d", "d" },
        { 4, 2, 32, 4, "Main::Leaf--e", "e" }
    };
    inline constexpr TypeInfo g_typeinfo_MainᕒLeaf = {
        27,
        40,
        5,
        LayoutTag::Ref,
        nullptr,
        nullptr,
        0,
        g_ftable_MainᕒLeaf,
        5,
        nullptr,
        0,
        "Main::Leaf",
        true
    };
    extern thread_local GCAllocator<MainᕒLeaf> MainᕒLeaf_allocator;
}

using SomeᐸMainᕒLeafᐳ = ᐸRuntimeᐳ::XSome<MainᕒLeaf*>;
namespace ᐸRuntimeᐳ {
    inline constexpr uint32_t g_supertypes_SomeᐸMainᕒLeafᐳ[1] = { 29 };
    inline constexpr TypeInfo g_typeinfo_SomeᐸMainᕒLeafᐳ = {
        26,
        8,
        1,
        LayoutTag::Value,
        "1",
        g_supertypes_SomeᐸMainᕒLeafᐳ,
        1,
        nullptr,
        0,
        nullptr,
        0,
        "Some<Main::Leaf>",
        true
    };
}

using OptionᐸMainᕒLeafᐳ = ᐸRuntimeᐳ::XOption<MainᕒLeaf*>;
namespace ᐸRuntimeᐳ { 
    inline constexpr TypeInfo g_typeinfo_OptionᐸMainᕒLeafᐳ = {
        29,
        16,
        2,
        LayoutTag::Value,
        "20",
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "Option<Main::Leaf>",
        true
    };
}

class MainᕒNode {
public:
    OptionᐸMainᕒLeafᐳ l;    
    OptionᐸMainᕒLeafᐳ r;    
    Int p;
    //All constructor and assignment defaults
};
namespace ᐸRuntimeᐳ {
    inline constexpr FieldOffsetInfo g_ftable_MainᕒNode[3] = {
        { 5, 29, 0, 0, "Main::Node--l", "l" },
        { 6, 29, 16, 2, "Main::Node--r", "r" },
        { 7, 2, 32, 4, "Main::Node--p", "p" }
    };
    inline constexpr TypeInfo g_typeinfo_MainᕒNode = {
        28,
        40,
        5,
        LayoutTag::Ref,
        "20200",
        nullptr,
        0,
        g_ftable_MainᕒNode,
        3,
        nullptr,
        0,
        "Main::Node",
        true
    };
    extern thread_local GCAllocator<MainᕒNode> MainᕒNode_allocator;
}

namespace ᐸRuntimeᐳ { 
    thread_local GCAllocator<MainᕒLeaf> MainᕒLeaf_allocator(&g_typeinfo_MainᕒLeaf);

    template<> const TypeInfo* XOption<MainᕒLeaf*>::s_someTypeInfo = &ᐸRuntimeᐳ::g_typeinfo_SomeᐸMainᕒLeafᐳ;

    thread_local GCAllocator<MainᕒNode> MainᕒNode_allocator(&g_typeinfo_MainᕒNode);
}

BOOST_AUTO_TEST_SUITE(GC_Basics)

BOOST_AUTO_TEST_CASE(ROOTS_ALL_LIVE) {
    auto l = ᐸRuntimeᐳ::MainᕒLeaf_allocator.allocate(1_i, 2_i, 3_i, 4_i, 5_i);
    auto n = ᐸRuntimeᐳ::MainᕒNode_allocator.allocate(OptionᐸMainᕒLeafᐳ{SomeᐸMainᕒLeafᐳ{l}}, OptionᐸMainᕒLeafᐳ::none, 42_i);

    ᐸRuntimeᐳ::test_collect({n, l}, {});
}

BOOST_AUTO_TEST_CASE(ROOTS_ALL_DEAD) {
    auto l = ᐸRuntimeᐳ::MainᕒLeaf_allocator.allocate(1_i, 2_i, 3_i, 4_i, 5_i);
    ᐸRuntimeᐳ::MainᕒNode_allocator.allocate(OptionᐸMainᕒLeafᐳ{SomeᐸMainᕒLeafᐳ{l}}, OptionᐸMainᕒLeafᐳ::none, 42_i);

    ᐸRuntimeᐳ::test_collect({}, {});
}

BOOST_AUTO_TEST_CASE(ROOTS_ALL_LIVE_DEAD) {
    auto l = ᐸRuntimeᐳ::MainᕒLeaf_allocator.allocate(1_i, 2_i, 3_i, 4_i, 5_i);
    auto n = ᐸRuntimeᐳ::MainᕒNode_allocator.allocate(OptionᐸMainᕒLeafᐳ{SomeᐸMainᕒLeafᐳ{l}}, OptionᐸMainᕒLeafᐳ::none, 42_i);

    ᐸRuntimeᐳ::test_collect({n, l}, {});
    ᐸRuntimeᐳ::test_collect({}, {});
}

BOOST_AUTO_TEST_CASE(ROOTS_ALL_LIVE_SHARE_SWITCH_AND_DIE) {
}

BOOST_AUTO_TEST_CASE(INDIRECT_LIVE) {
}

BOOST_AUTO_TEST_CASE(INDIRECT_DEAD_YOUNG) {
}

BOOST_AUTO_TEST_CASE(INDIRECT_PROC_DIE_OLD) {
}

BOOST_AUTO_TEST_CASE(INDIRECT_PROC_SHARE_YOUNG_DIE_OLD) {
}

BOOST_AUTO_TEST_CASE(INDIRECT_PROC_SHARE_YOUNG_ROOT_XYOUNG_XROOT_DIE_OLD) {
}

BOOST_AUTO_TEST_CASE(INDIRECT_PROC_SHARE_YOUNG_ROOT_XROOT_XYOUNG_DIE_OLD) {
}

BOOST_AUTO_TEST_SUITE_END() //GC_Basics

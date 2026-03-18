#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

#include "../runtime/allocator/alloc.h"

namespace ᐸRuntimeᐳ
{
    enum class RColor : uint64_t
    {
        Red,
        Black,
        BBlack
    };

    //TODO: when this is hooked up to the GC we can drop this and use the page type info instead
    enum class PosRBTreeTag : uint64_t
    {
        Leaf,
        Node
    };

    template<typename T, int64_t K> class PosRBTreeNode;

    template<typename T, int64_t K> 
    class PosRBTreeLeaf
    {
    public:
        int64_t count;
        std::array<T, K> data;

        constexpr PosRBTreeLeaf() : count(0) { std::memset((void*)this->data.data(), 0, sizeof(T) * K); }
        constexpr PosRBTreeLeaf(const PosRBTreeLeaf& other) = default;

        PosRBTreeLeaf(std::initializer_list<T> args)
        {
            assert(args.size() != 0);
            assert(args.size() <= K);

            std::memset((void*)this->data.data(), 0, sizeof(T) * K);
            std::copy(args.begin(), args.end(), this->data.begin());

            this->count = args.size();
        }
    };

    template<typename T, int64_t K>
    consteval TypeInfo g_typeinfo_PosRBTreeLeaf_generate(uint32_t tid, uint16_t tslots, const char* mask, const char* tname)
    {
        return TypeInfo{
            tid,
            sizeof(PosRBTreeLeaf<T, K>),
            byteSizeToSlotCount(sizeof(PosRBTreeLeaf<T, K>)),
            LayoutTag::ArrayRef,
            tslots,
            mask,
            tname,
            nullptr
        };
    }

    template<typename T, int64_t K>
    union PosRBTreeUnion
    {
        //empty tree is where boxed union typeinfo is nullptr
        PosRBTreeLeaf<T, K>* leaf;
        PosRBTreeNode<T, K>* node;

        constexpr PosRBTreeUnion() : leaf() {}
        constexpr PosRBTreeUnion(const PosRBTreeUnion& other) = default;
        constexpr PosRBTreeUnion(PosRBTreeLeaf<T, K>* l) : leaf(l) {}
        constexpr PosRBTreeUnion(PosRBTreeNode<T, K>* n) : node(n) {}
    };
    template<typename T, int64_t K>
    using PosRBTreeRepr = BoxedUnion<PosRBTreeUnion<T, K>>;

    template<typename T, int64_t K> 
    class PosRBTreeNode
    {
    public:
        int64_t count;
        RColor color;
        PosRBTreeRepr<T, K> left;
        PosRBTreeRepr<T, K> right;
    };

    template<typename T, int64_t K> 
    consteval TypeInfo g_typeinfo_PosRBTreeNode_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo{
            tid,
            sizeof(PosRBTreeNode<T, K>),
            byteSizeToSlotCount(sizeof(PosRBTreeNode<T, K>)),
            LayoutTag::Ref,
            BSQ_TYPEINFO_NO_ESLOT,
            "002020",
            tname,
            nullptr
        };
    }

    ////
    //Note that we tag each template to keep the types distinct because we have the static allocator/type info! 
    //For now we probably want to mostly PIMPL the persistent tree logic and keep wrappers in the class to avoid code bloat but we can always change this later.
    ////
    template<typename T, int64_t K, uint32_t TreeID>
    class PosRBTree
    {
    public:
        PosRBTreeRepr<T, K> repr;

        static const TypeInfo* s_leaftypeinfo;
        thread_local static GCAllocator<PosRBTreeLeaf<T, K>>* s_leafallocator;

        static const TypeInfo* s_nodetypeinfo;
        thread_local static GCAllocator<PosRBTreeNode<T, K>>* s_nodeallocator;

        static PosRBTree<T, K, TreeID> mkwleaf(PosRBTreeLeaf<T, K>* leaf) 
        {
            return PosRBTree<T, K, TreeID>(BoxedUnion<PosRBTreeUnion<T, K>>(s_leaftypeinfo, PosRBTreeUnion<T, K>(leaf)));
        }

        constexpr int64_t count() const
        {
            if(this->repr.typeinfo == nullptr) {
                return 0;
            }
            else {
                if(this->repr.typeinfo == s_leaftypeinfo) {
                    return this->repr.data.leaf->count;
                }
                else {
                    return this->repr.data.node->count;
                }
            }
        }

        PosRBTreeLeaf<T, K>* getLeaf(int64_t index) const
        {
            if(this->repr.typeinfo == s_leaftypeinfo) {
                return this->repr.data.leaf;
            }
            else {
                assert(false); // Not Implemented: full getLeaf for PosRBTree
                return nullptr;
            }
        }

        T& get(int64_t index) const
        {
            if(this->repr.typeinfo == s_leaftypeinfo) {
                return this->repr.data.leaf->data[index];
            }
            else {
                assert(false); // Not Implemented: full getLeaf for PosRBTree
            }
        }
    };

    template<typename T, int64_t K, uint32_t TreeID> 
    consteval TypeInfo g_typeinfo_PosRBTree_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo {
            tid,
            sizeof(PosRBTree<T, K, TreeID>),
            byteSizeToSlotCount(sizeof(PosRBTree<T, K, TreeID>)),
            LayoutTag::Tagged,
            BSQ_TYPEINFO_NO_ESLOT,
            "20",
            tname,
            nullptr
        };
    }
}

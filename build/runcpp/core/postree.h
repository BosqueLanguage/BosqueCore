#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

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

    class PosRBTreeLeafEmpty 
    {
    };
    
    consteval TypeInfo g_typeinfo_PosRBTreeLeafEmpty_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo{
            tid,
            8,
            1,
            LayoutTag::Value,
            BSQ_PTR_MASK_LEAF,
            tname,
            nullptr
        };
    }

    template<typename T, int64_t K> 
    class PosRBTreeLeaf
    {
    public:
        int64_t count;
        T data[K];
    };

    template<typename T, int64_t K>
    consteval TypeInfo g_typeinfo_PosRBTreeLeaf_generate(uint32_t tid, const char* mask, const char* tname)
    {
        return TypeInfo{
            tid,
            sizeof(PosRBTreeLeaf<T, K>),
            byteSizeToSlotCount(sizeof(PosRBTreeLeaf<T, K>)),
            LayoutTag::Ref,
            mask,
            tname,
            nullptr
        };
    }

    template<typename T, int64_t K>
    union PosRBTreeUnion
    {
        PosRBTreeLeafEmpty emptyleaf;
        PosRBTreeLeaf<T, K>* leaf;
        PosRBTreeNode<T, K>* node;

        constexpr PosRBTreeUnion() : leaf() {}
        constexpr PosRBTreeUnion(const PosRBTreeUnion& other) = default;
        constexpr PosRBTreeUnion(PosRBTreeLeafEmpty l) : emptyleaf(l) {}
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
            "002020",
            tname,
            nullptr
        };
    }

    template<typename T, int64_t K, uint32_t TreeID>
    class PosRBTree
    {
    public:
        PosRBTreeRepr<T, K> repr;

        inline static consteval uint32_t getEmptyLeafIDFrom(uint32_t treeid) { return treeid - 3; }
        inline static consteval uint32_t getLeafIDFrom(uint32_t treeid) { return treeid - 2; }
        inline static consteval uint32_t getNodeIDFrom(uint32_t treeid) { return treeid - 1; }

        constexpr int64_t count() const
        {
            if(this->repr.typeinfo->bsqtypeid == getEmptyLeafIDFrom(TreeID)) {
                return 0;
            }
            else if(this->repr.typeinfo->bsqtypeid == getLeafIDFrom(TreeID)) {
                return this->repr.data.leaf->count;
            }
            else {
                return this->repr.data.node->count;
            }
        }

        PosRBTreeLeaf<T, K>* getLeaf(int64_t index) const
        {
            if(this->repr.typeinfo->bsqtypeid == getLeafIDFrom(TreeID)) {
                return this->repr.data.leaf;
            }
            else {
                assert(false); // Not Implemented: full getLeaf for PosRBTree
                return nullptr;
            }
        }

        T& get(int64_t index) const
        {
            if(this->repr.typeinfo->bsqtypeid == getLeafIDFrom(TreeID)) {
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
            "20",
            tname,
            nullptr
        };
    }
}

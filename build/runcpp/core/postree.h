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

    template<typename T, size_t K> class PosRBTreeNode;

    class PosRBTreeLeafEmpty 
    {
    };
    
    constexpr TypeInfo g_typeinfo_PosRBTreeLeafEmpty_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo {
            tid,
            8,
            1,
            LayoutTag::Value,
            BSQ_PTR_MASK_LEAF,
            tname,
            nullptr
        };
    }

    template<typename T, size_t K> 
    class PosRBTreeLeaf
    {
    public:
        size_t count;
        T data[K];
    };

    template<typename T, size_t K>
    constexpr TypeInfo g_typeinfo_PosRBTreeLeaf_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo {
            tid,
            sizeof(PosRBTreeLeaf<T, K>),
            byteSizeToSlotCount(sizeof(PosRBTreeLeaf<T, K>)),
            LayoutTag::Ref,
            BSQ_PTR_MASK_LEAF,
            tname,
            nullptr
        };
    }

    template<typename T, size_t K>
    union PosRBTreeUnion
    {
        PosRBTreeLeafEmpty bbleaf;
        PosRBTreeLeaf<T, K>* leaf;
        PosRBTreeNode<T, K>* node;

        constexpr PosRBTreeUnion() : leaf() {}
        constexpr PosRBTreeUnion(const PosRBTreeUnion& other) = default;
        constexpr PosRBTreeUnion(PosRBTreeLeafEmpty l) : bbleaf(l) {}
        constexpr PosRBTreeUnion(PosRBTreeLeaf<T, K>* l) : leaf(l) {}
        constexpr PosRBTreeUnion(PosRBTreeNode<T, K>* n) : node(n) {}
    };
    template<typename T, size_t K>
    using PosRBTreeRepr = BoxedUnion<PosRBTreeUnion<T, K>>;

    template<typename T, size_t K> 
    class PosRBTreeNode
    {
    public:
        size_t count;
        RColor color;
        PosRBTreeRepr<T, K> left;
        PosRBTreeRepr<T, K> right;

        constexpr TypeInfo generateTypeInfo(uint32_t tid, const char* tname) const
        {
            return TypeInfo {
                tid,
                sizeof(PosRBTreeNode<T, K>),
                byteSizeToSlotCount(sizeof(PosRBTreeNode<T, K>)),
                LayoutTag::Ref,
                "002020",
                tname,
                nullptr
            };
        }
    };

    template<typename T, size_t K>
    class PosRBTree
    {
    public:
        static TypeInfo* bbleaftype;
        static TypeInfo* leaftype;
        static TypeInfo* nodetype;
        
        PosRBTreeRepr<T, K> repr;
        
        constexpr TypeInfo generateTypeInfo(uint32_t tid, const char* tname) const
        {
            return TypeInfo {
                tid,
                sizeof(PosRBTreeRepr<T, K>),
                byteSizeToSlotCount(sizeof(PosRBTreeRepr<T, K>)),
                LayoutTag::Ref,
                "002020",
                tname,
                nullptr
            };
        }

        constexpr size_t count() const
        {
            if(this->repr.typeinfo == PosRBTree<T, K>::bbleaftype) {
                return 0;
            }
            else if(this->repr.typeinfo == PosRBTree<T, K>::leaftype) {
                return this->repr.leaf->count;
            }
            else {
                return this->repr.node->count;
            }
        }

        template<typename T, size_t K>
        PosRBTreeLeaf<T, K>* getLeaf(const PosRBTree<T, K>* tree, size_t index) const
        {
            if(this->repr.typeinfo == PosRBTree<T, K>::leaftype) {
                return this->repr.leaf;
            }
            else {
                assert(false); // Not Implemented: full getLeaf for PosRBTree
                return nullptr;
            }
        }

        template<typename T, size_t K>
        T& get(const PosRBTree<T, K>* tree, size_t index)
        {
            if(this->repr.typeinfo == PosRBTree<T, K>::leaftype) {
                return this->repr.leaf->data[index];
            }
            else {
                assert(false); // Not Implemented: full getLeaf for PosRBTree
                return nullptr;
            }
        }
    };
}

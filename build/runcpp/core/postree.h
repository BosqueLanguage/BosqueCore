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

    template<typename T, size_t K> 
    class PosRBTreeLeaf
    {
    public:
        size_t count;
        T data[K];
    };

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
    };

    template<typename T, size_t K>
    class PosRBTree
    {
    public:
        static TypeInfo* bbleaftype;
        static TypeInfo* leaftype;
        static TypeInfo* nodetype;
        
        PosRBTreeRepr<T, K> repr;
        
        constexpr size_t count() const
        {
            if(tree->repr.xxxx == PosRBTreeTag::Leaf) {
                return tree->repr.cstrtree.leaf.count;
            }
            else {
                return tree->cstrtree.node.count;
            }
        }

        template<typename T, size_t K>
        PosRBTreeLeaf<T, K>* getLeaf(const PosRBTree<T, K>* tree, size_t index) const
        {
            if(tree->tag == PosRBTreeTag::Leaf) {
                return &tree->cstrtree.leaf;
            }
            else {
                assert(false); // Not Implemented: full getLeaf for PosRBTree
                return nullptr;
            }
        }

        template<typename T, size_t K>
        T& get(const PosRBTree<T, K>* tree, size_t index)
        {
            if(tree->tag == PosRBTreeTag::Leaf) {
                return tree->cstrtree.leaf.data[index];
            }
            else {
                assert(false); // Not Implemented: full get for PosRBTree
            }
        }
    };
}

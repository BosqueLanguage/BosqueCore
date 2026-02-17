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

    template<typename T, size_t K> class PosRBTree;

    template<typename T, size_t K> 
    class PosRBTreeLeaf
    {
    public:
        size_t count;
        T data[K];
    };

    template<typename T, size_t K> 
    class PosRBTreeNode
    {
    public:
        size_t count;
        RColor color;
        PosRBTree<T, K>* left;
        PosRBTree<T, K>* right;
    };

    template<typename T, size_t K>
    union PosRBTreeUnion
    {
        PosRBTreeLeaf<T, K> leaf;
        PosRBTreeNode<T, K> node;

        constexpr PosRBTreeUnion() : leaf() {}
        constexpr PosRBTreeUnion(const PosRBTreeUnion& other) = default;
        constexpr PosRBTreeUnion(PosRBTreeLeaf<T, K>* l) : leaf(l) {}
        constexpr PosRBTreeUnion(PosRBTreeNode<T, K>* n) : node(n) {}
    };    

    template<typename T, size_t K>
    class PosRBTree
    {
    public:
        PosRBTreeTag tag;
        PosRBTreeUnion<T, K> cstrtree;

        constexpr size_t count() const
        {
            if(this->tag == PosRBTreeTag::Leaf) {
                return this->cstrtree.leaf.count;
            }
            else {
                return this->cstrtree.node.count;
            }
        }

        PosRBTreeLeaf<T, K>* getLeaf(size_t index) const
        {
            if(this->tag == PosRBTreeTag::Leaf) {
                return &this->cstrtree.leaf;
            }
            else {
                assert(false); // Not Implemented: full getLeaf for PosRBTree
                return nullptr;
            }
        }

        T& get(size_t index)
        {
            if(this->tag == PosRBTreeTag::Leaf) {
                return this->cstrtree.leaf.data[index];
            }
            else {
                assert(false); // Not Implemented: full get for PosRBTree
            }
        }
    };
}

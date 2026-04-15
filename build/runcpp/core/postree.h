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

        // TODO: we need to investigate whether we should really have insert be void
        //       and modify the contents of data
        void insert(int64_t index, const T& value)
        {
            assert(index < K);
            assert(this->count < K);

            this->data[index] = value;
            this->count++;
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
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            tname
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
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            tname
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

        static PosRBTreeRepr<T, K> mkwleaf_repr(PosRBTreeLeaf<T, K>* leaf) 
        {
            return PosRBTreeRepr<T, K>(s_leaftypeinfo, PosRBTreeUnion<T, K>(leaf));
        }

        static PosRBTreeRepr<T, K> mkwnode_repr(PosRBTreeNode<T, K>* node) 
        {
            return PosRBTreeRepr<T, K>(s_nodetypeinfo, PosRBTreeUnion<T, K>(node));
        }

        static PosRBTree<T, K, TreeID> mkwleaf(PosRBTreeLeaf<T, K>* leaf) 
        {
            return PosRBTree<T, K, TreeID>(mkwleaf_repr(leaf));
        }

       static PosRBTree<T, K, TreeID> mkwnode(PosRBTreeNode<T, K>* node) 
        {
            return PosRBTree<T, K, TreeID>(mkwnode_repr(node));
        }

        static int64_t checkRBPathLengthInvariant(const PosRBTreeRepr<T, K>& t)
        {
            if(t.typeinfo == s_leaftypeinfo) {
                return 0;
            }
            
            const int lc = checkRBPathLengthInvariant(t.data.node->right);
            if(lc == -1) {
                return -1;
            }

            const int rc = checkRBPathLengthInvariant(t.data.node->right);
            if(rc == -1) {
                return -1;
            }

            if(lc != rc) { // black height mismatch
                return -1;
            }

            return t.data.node->color == RColor::Black 
                ? lc + 1
                : lc;
        }

        static bool checkRBChildColorInvariant(const PosRBTreeRepr<T, K>& t)
        {
            if(t.typeinfo != s_nodetypeinfo) {
                return true;
            }

            if(t.data.node->color == RColor::Red) {
                const bool islred = t.data.node->left.typeinfo == s_nodetypeinfo 
                    ? t.data.node->left.data.node->color == RColor::Red
                    : false;
                const bool isrred = t.data.node->right.typeinfo == s_nodetypeinfo 
                    ? t.data.node->right.data.node->color == RColor::Red
                    : false;

                return !(islred || isrred);
            }

            return checkRBChildColorInvariant(t.data.node->left)
                && checkRBChildColorInvariant(t.data.node->right);
        }

        static bool checkRBInvariants(const PosRBTreeRepr<T, K>& t)
        {
            return checkRBChildColorInvariant(t) && checkRBPathLengthInvariant(t) >= 0;
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

        static T& get_helper(int64_t index, const PosRBTreeRepr<T, K>& cur) 
        {
            assert(cur.typeinfo != nullptr);

            if(cur.typeinfo == s_leaftypeinfo) {
                return cur.data.leaf->data[index];
            }
            else {
                const int64_t count = cur.data.node->count;
                if(index < count) {
                    return get_helper(index, cur.data.node->left);
                }
                else {
                    return get_helper(index - count, cur.data.node->right);
                }
            }
        }

        T& get(int64_t index) const
        {
            return get_helper(index, this->repr);
        }

        static PosRBTree<T, K, TreeID> insert_helper(int64_t index, const T& value, const PosRBTreeRepr<T, K>& t)
        {
            assert(t.typeinfo != nullptr);

            if(t.typeinfo == s_leaftypeinfo) {
                if(t.data.leaf->count < K) {
                    // dont create a new node, our target leaf has enough space
                    t.data.leaf->insert(index, value);
                    return mkwleaf(t.data.leaf);
                }
                else {
                    PosRBTreeLeaf<T, K>* nleaf;
                    if(index < t.data.leaf->count) {
                        // create new node containing only last element of full leaf
                        const T& last = t.data.leaf->data.back();
                        nleaf = s_leafallocator->allocate(last);

                        // shift and insert
                        std::copy(t.data.leaf->data.begin() + index,t.data.leaf->data.end() - 1, t.data.leaf->data.begin() + index + 1);
                        t.data.leaf->count--;
                        t.data.leaf->insert(index, value);
                    }
                    else {
                        nleaf = s_leafallocator->allocate(value);
                    }

                    PosRBTreeNode<T, K>* nn = s_nodeallocator->allocate(t.data.leaf->count, RColor::Red, t, mkwleaf_repr(nleaf));
                    return mkwnode(nn);
                }
            }
            else {
                // !!!!!! TODO: need balancing !!!!!!!
                const int64_t count = t.data.node->count;
                PosRBTreeNode<T, K>* nn;

                // !!!!! TODO: need to improve the count thing and document its purpose !!!!!!
                // (grabbing the count fields value from a node or leaf here feels weird since we dont
                // know the type of that subtree and just rely on its positioning for that to work)
                if(index < count) {
                    auto nl = insert_helper(index, value, t.data.node->left);
                    nn = s_nodeallocator->allocate(nl.repr.data.node->count, RColor::Red, nl.repr, t.data.node->right);
                }
                else {
                    auto nr = insert_helper(index - count, value, t.data.node->right);
                    nn =  s_nodeallocator->allocate(t.data.node->count, RColor::Red, t.data.node->left, nr.repr);
                }

                return mkwnode(nn);
            }
        }

        static PosRBTree<T, K, TreeID> insert(int64_t index, const T& value, const PosRBTree<T, K, TreeID>& t) 
        {
            PosRBTree<T, K, TreeID> res(insert_helper(index, value, t.repr));

            assert(checkRBInvariants(res.repr));

            return res;
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
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            tname
        };
    }
}
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

        constexpr PosRBTreeLeaf() : count(0) { ; }
        constexpr PosRBTreeLeaf(const PosRBTreeLeaf& other) = default;

        template<typename Iter>
        requires std::random_access_iterator<Iter>
        PosRBTreeLeaf(Iter start, Iter end) 
        { 
            const int64_t size = std::distance(start, end);
            assert(size <= K);
            std::copy(start, end, this->data.begin());
            this->count = size; 
        }

        PosRBTreeLeaf(std::initializer_list<T> args)
        {
            assert(args.size() != 0);
            assert(args.size() <= K);

            std::copy(args.begin(), args.end(), this->data.begin());
            this->count = args.size();
        }

        T back() const
        {
            return this->data.back();
        }

        PosRBTreeLeaf subset(int64_t index, int64_t length) const
        {
            return PosRBTreeLeaf(this->data.begin() + index, this->data.begin() + index + length);
        }

        PosRBTreeLeaf subsetinsert(int64_t subset_index, int64_t insert_index, int64_t length, const T& value) const
        {
            assert(insert_index < K);
            assert(subset_index + length < K);
            assert(this->count <= K);

            PosRBTreeLeaf nleaf;
            std::copy(this->data.begin() + subset_index, 
                      this->data.begin() + subset_index + insert_index, 
                      nleaf.data.begin());
            std::copy(this->data.begin() + subset_index + insert_index, 
                      this->data.begin() + subset_index + length, 
                      nleaf.data.begin() + insert_index + 1);

            nleaf.data[insert_index] = value;
            nleaf.count = length + 1;

            return nleaf;
        }

        PosRBTreeLeaf insert(int64_t index, const T& value) const
        {
            assert(index < K);
            assert(this->count < K);
          
            PosRBTreeLeaf nleaf;
            if(index > 0) {
                std::copy(this->data.cbegin(), this->data.cbegin() + index, nleaf.data.begin());
            }

            if(index < this->count) {
                std::copy(this->data.cbegin() + index, this->data.cbegin() + this->count, nleaf.data.begin() + index + 1);               
            }

            nleaf.data[index] = value;
            nleaf.count = this->count + 1;

            return nleaf;
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

        static PosRBTreeRepr<T, K> mkwleafRepr(PosRBTreeLeaf<T, K>* leaf) 
        {
            return PosRBTreeRepr<T, K>(s_leaftypeinfo, PosRBTreeUnion<T, K>(leaf));
        }

        static PosRBTreeRepr<T, K> mkwnodeRepr(PosRBTreeNode<T, K>* node) 
        {
            return PosRBTreeRepr<T, K>(s_nodetypeinfo, PosRBTreeUnion<T, K>(node));
        }

        static PosRBTree<T, K, TreeID> mkwleaf(PosRBTreeLeaf<T, K>* leaf) 
        {
            return PosRBTree<T, K, TreeID>(mkwleafRepr(leaf));
        }

       static PosRBTree<T, K, TreeID> mkwnode(PosRBTreeNode<T, K>* node) 
        {
            return PosRBTree<T, K, TreeID>(mkwnodeRepr(node));
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

        static bool checkRBInvariants(const PosRBTree<T, K, TreeID>& tree)
        {
            return checkRBChildColorInvariant(tree.repr) && checkRBPathLengthInvariant(tree.repr) >= 0;
        }

        static bool validateRedNode(const PosRBTreeRepr<T, K>& cur)
        {
            if(cur.typeinfo != s_nodetypeinfo || cur.data.node->color != RColor::Red) {
                return false;
            }
            
            return true; 
        }

        static bool validateBlackNode(const PosRBTreeRepr<T, K>& cur)
        {
            if(cur.typeinfo != s_nodetypeinfo || cur.data.node->color != RColor::Black) {
                return false;
            }
            
            return true;
        }

        // double red violation on the LL side (tleft = Node{Red, _, Node{Red, _ a, b}, c})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_LL(const PosRBTreeRepr<T, K>& cur)
        {
            const PosRBTreeRepr<T, K>& l  = cur.data.node->left;
            const PosRBTreeRepr<T, K>& ll = l.data.node->left;
            if(!validateBlackNode(cur) || !validateRedNode(l) || !validateRedNode(ll)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& lll = ll.data.node->left;
            const PosRBTreeRepr<T, K>& llr = ll.data.node->right;
            const PosRBTreeRepr<T, K>& lr  = l.data.node->right;
            const PosRBTreeRepr<T, K>& r   = cur.data.node->right;
            const PosRBTreeRepr<T, K> nl = mkwnodeRepr(s_nodeallocator->allocate(lll.data.node->count + llr.data.node->count, RColor::Black, lll, llr));
            const PosRBTreeRepr<T, K> nr = mkwnodeRepr(s_nodeallocator->allocate(lr.data.node->count + r.data.node->count, RColor::Red, lr, r));
            return mkwnodeRepr(s_nodeallocator->allocate(nl.data.node->count + nr.data.node->count, RColor::Red, nl, nr));
        }

        // double red violation on the LR side (tleft = Node{Red, _, a, Node{Red, _, b, c}})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_LR(const PosRBTreeRepr<T, K>& cur)
        {
            const PosRBTreeRepr<T, K>& l  = cur.data.node->left;
            const PosRBTreeRepr<T, K>& lr = l.data.node->right;
            if(!validateBlackNode(cur) || !validateRedNode(l) || !validateRedNode(lr)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& ll  = l.data.node->left;
            const PosRBTreeRepr<T, K>& lrl = lr.data.node->left;
            const PosRBTreeRepr<T, K>& lrr = lr.data.node->right;
            const PosRBTreeRepr<T, K>& r   = cur.data.node->right;
            const PosRBTreeRepr<T, K> nl = mkwnodeRepr(s_nodeallocator->allocate(ll.data.node->count + lrl.data.node->count, RColor::Black, ll, lrl));
            const PosRBTreeRepr<T, K> nr = mkwnodeRepr(s_nodeallocator->allocate(lrr.data.node->count + r.data.node->count, RColor::Black, lrr, r));
            return mkwnodeRepr(s_nodeallocator->allocate(nl.data.node->count + nr.data.node->count, RColor::Red, nl, nr));
        }

        // double red violation on the RL side (tright = Node{Red, _, Node{Red, _, b, c}, d})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_RL(const PosRBTreeRepr<T, K>& cur)
        {
            const PosRBTreeRepr<T, K>& r  = cur.data.node->right;
            const PosRBTreeRepr<T, K>& rl = r.data.node->left;
            if(!validateBlackNode(cur) || !validateRedNode(r) || !validateRedNode(rl)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l   = cur.data.node->left;
            const PosRBTreeRepr<T, K>& rll = rl.data.node->left;
            const PosRBTreeRepr<T, K>& rlr = rl.data.node->right;
            const PosRBTreeRepr<T, K>& rr  = r.data.node->right;
            const PosRBTreeRepr<T, K> nl = mkwnodeRepr(s_nodeallocator->allocate(l.data.node->count + rll.data.node->count, RColor::Black, l, rll));
            const PosRBTreeRepr<T, K> nr = mkwnodeRepr(s_nodeallocator->allocate(rlr.data.node->count + rr.data.node->count, RColor::Black, rlr, rr));
            return mkwnodeRepr(s_nodeallocator->allocate(nl.data.node->count + nr.data.node->count, RColor::Red, nl, nr));
        }

        // double red violation on the RR side (tright = Node{Red, _, b, Node{Red, _, c, d}})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_RR(const PosRBTreeRepr<T, K>& cur)
        {
            const PosRBTreeRepr<T, K>& r  = cur.data.node->right;
            const PosRBTreeRepr<T, K>& rr = r.data.node->right;
            if(!validateBlackNode(cur) || !validateRedNode(r) || !validateRedNode(rr)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l   = cur.data.node->left;
            const PosRBTreeRepr<T, K>& rl  = r.data.node->left;
            const PosRBTreeRepr<T, K>& rrl = rr.data.node->left;
            const PosRBTreeRepr<T, K>& rrr = rr.data.node->right;
            const PosRBTreeRepr<T, K> nl = mkwnodeRepr(s_nodeallocator->allocate(l.data.node->count + rl.data.node->count, RColor::Black, l, rl));
            const PosRBTreeRepr<T, K> nr = mkwnodeRepr(s_nodeallocator->allocate(rrl.data.node->count + rrr.data.node->count, RColor::Black, rrl, rrr));
            return mkwnodeRepr(s_nodeallocator->allocate(nl.data.node->count + nr.data.node->count, RColor::Red, nl, nr));
        }

        static PosRBTreeRepr<T, K> balance(const PosRBTreeRepr<T, K>& cur)
        {
            if(auto res = balancehelper_RR_LL(cur)) {
                return *res;
            }
            else if(auto res = balancehelper_RR_LR(cur)) {
                return *res;
            }
            else if(auto res = balancehelper_RR_RL(cur)) {
                return *res;
            }
            else if(auto res = balancehelper_RR_RR(cur)) {
                return *res;
            }
            else {
                return cur;
            }
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

        static T gethelper(int64_t index, const PosRBTreeRepr<T, K>& cur) 
        {
            assert(cur.typeinfo != nullptr);

            if(cur.typeinfo == s_leaftypeinfo) {
                return cur.data.leaf->data[index];
            }
            else {
                const int64_t lcount = cur.data.node->left.data.node->count;
                if(index < lcount) {
                    return gethelper(index, cur.data.node->left);
                }
                else {
                    return gethelper(index - lcount, cur.data.node->right);
                }
            }
        }

        T get(int64_t index) const
        {
            return gethelper(index, this->repr);
        }

        static PosRBTreeRepr<T, K> inserthelper(int64_t index, const T& value, const PosRBTreeRepr<T, K>& cur)
        {
            assert(cur.typeinfo != nullptr);

            if(cur.typeinfo == s_leaftypeinfo) {
                const int64_t cur_count = cur.data.leaf->count;
                if(cur_count < K) {
                    return mkwleafRepr(s_leafallocator->allocate(cur.data.leaf->insert(index, value)));
                }
                else {
                    PosRBTreeRepr<T, K> nl, nr;
                    if(index == 0) {
                        nl = mkwleafRepr(s_leafallocator->allocate(value));
                        nr = cur;
                    }
                    else if(index >= K - 1) {
                        nl = cur; 
                        nr = mkwleafRepr(s_leafallocator->allocate(value));
                    }
                    else {
                        PosRBTreeLeaf<T, K> nlleaf, nrleaf;
                        const int64_t midpt = cur.data.leaf->count / 2;
                        if(index < midpt) {
                            nlleaf = cur.data.leaf->subsetinsert(0, index, midpt, value);
                            nrleaf = cur.data.leaf->subset(midpt, K - midpt);
                        }
                        else {
                            nlleaf = cur.data.leaf->subset(0, midpt);
                            nrleaf = cur.data.leaf->subsetinsert(midpt, index, K - midpt, value);
                        }

                        nl = mkwleafRepr(s_leafallocator->allocate(nlleaf));
                        nr = mkwleafRepr(s_leafallocator->allocate(nrleaf));
                    }

                    return mkwnodeRepr(s_nodeallocator->allocate(cur_count + 1, RColor::Red, nl, nr)); 
                }
            }
            else {
                PosRBTreeRepr<T, K> nl, nr;
                const int64_t lcount = cur.data.node->left.data.node->count;
                if(index < lcount) {
                    nl = inserthelper(index, value, cur.data.node->left);
                    nr = cur.data.node->right;
                }
                else {
                    nl = cur.data.node->left;
                    nr = inserthelper(index - lcount, value, cur.data.node->right); 
                }

                return balance(mkwnodeRepr(s_nodeallocator->allocate(nl.data.node->count + nr.data.node->count, RColor::Red, nl, nr)));
            }
        }

        PosRBTree<T, K, TreeID> insert(int64_t index, const T& value) const
        {
            PosRBTree<T, K, TreeID> res(inserthelper(index, value, this->repr));
            if(res.repr.typeinfo == s_nodetypeinfo) {  
                res.repr.data.node->color = RColor::Black;
                res = PosRBTree<T, K, TreeID>(balance(res.repr));
            }

            assert(checkRBInvariants(res));

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
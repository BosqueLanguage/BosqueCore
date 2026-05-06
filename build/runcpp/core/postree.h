#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "boxed.h"

#include "../runtime/allocator/alloc.h"

#define BSQ_POSTREE_VALIDATE 1

#if BSQ_POSTREE_VALIDATE
#define BSQ_POSTREE_ASSERT(COND) assert(COND)
#else
#define BSQ_POSTREE_ASSERT(COND) ((void)0)
#endif

namespace ᐸRuntimeᐳ
{
    template<typename T, int64_t K>
    class PosRBTreeData
    {
    public:
        int64_t count;
        std::array<T, K> data;

        constexpr PosRBTreeData() : count(0) 
        {
            uint64_t* rawdata = reinterpret_cast<uint64_t*>(this->data.data()); 
            std::fill(rawdata, rawdata + K, 0); 
        }

        constexpr PosRBTreeData(const PosRBTreeData& other) = default;

        template<typename Iter>
        PosRBTreeData(Iter start, Iter end)
        {            
            const int64_t size = std::distance(start, end);
            assert(size <= K);

            uint64_t* rawdata = reinterpret_cast<uint64_t*>(this->data.data()); 
            std::fill(rawdata, rawdata + K, 0);

            std::copy(start, end, this->data.begin());
            this->count = size; 
        }

        PosRBTreeData(std::initializer_list<T> args)
        {
            assert(args.size() != 0);
            assert(args.size() <= K);

            uint64_t* rawdata = reinterpret_cast<uint64_t*>(this->data.data()); 
            std::fill(rawdata, rawdata + K, 0);

            std::copy(args.begin(), args.end(), this->data.begin());
            this->count = args.size();
        }

        T front() const
        {
            return this->data.front();
        }

        T back() const
        {
            return this->data.back();
        }

        T get(int64_t idx) const
        {
            return this->data.at(idx);
        }

        PosRBTreeData insert(int64_t index, const T& value) const
        {
            assert(index < K);
            assert(this->count < K);
          
            PosRBTreeData nleaf;
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

        PosRBTreeData remove(int64_t index) const
        {
            assert(index < this->count);
            assert(this->count > 1);

            PosRBTreeData nleaf;
            if(index > 0) {
                std::copy(this->data.cbegin(), this->data.cbegin() + index, nleaf.data.begin());
            }

            if(index + 1 < this->count) {
                std::copy(this->data.cbegin() + index + 1, this->data.cbegin() + this->count, nleaf.data.begin() + index);
            }

            nleaf.count = this->count - 1;
            return nleaf;
        }
    };

    enum class RColor : uint64_t
    {
        Red,
        Black
    };

    template<typename T, int64_t K> 
    class PosRBTreeNode
    {
    public:
        int64_t count;
        PosRBTreeNode* left;
        PosRBTreeNode* right;
        PosRBTreeData<T, K> data;

        RColor color;

    private:
        enum class InsertResultTag
        {
            Done,
            Tree
        };

        class InsertResult
        {
        public:
            InsertResultTag tag;
            PosRBTreeNode* tnode;

            static InsertResult makeDone(PosRBTreeNode* tnode) { return InsertResult{InsertResultTag::Done, tnode}; }
            static InsertResult makeTree(PosRBTreeNode* ptree) { return InsertResult{InsertResultTag::Tree, ptree}; }

            constexpr bool isDone() const { return this->tag == InsertResultTag::Done; }
            constexpr bool isTree() const { return this->tag == InsertResultTag::Tree; }
        };

        enum class DeleteResultTag : uint8_t
        {
            Done,
            Short
        };

        class DeleteResult
        {
        public:
            DeleteResultTag tag;
            PosRBTreeNode* tnode;

            static DeleteResult makeDone(PosRBTreeNode* tnode) { return DeleteResult{DeleteResultTag::Done, tnode}; }
            static DeleteResult makeShort(PosRBTreeNode* tnode) { return DeleteResult{DeleteResultTag::Short, tnode}; }

            constexpr bool isDone() const { return this->tag == DeleteResultTag::Done; }
            constexpr bool isShort() const { return this->tag == DeleteResultTag::Short; }
        };

        bool isReprLeaf() const { return (this->left == nullptr) & (this->right == nullptr); }
        bool isReprNode() const { return !isReprLeaf(); }

#if BSQ_POSTREE_VALIDATE
        int64_t checkRBPathLengthInvariant() const
        {
            if(this->isReprLeaf()) {
                return 0;
            }
            
            int64_t lc = (this->left !== nullptr) ? this->left->checkRBPathLengthInvariant() : 0;
            if(lc == -1) {
                return -1;
            }

            int64_t rc = (this->right !== nullptr) ? this->right->checkRBPathLengthInvariant() : 0;
            if(rc == -1) {
                return -1;
            }

            if(lc != rc) { // black height mismatch
                return -1;
            }

            return (this->color == RColor::Black) ? (lc + 1) : lc;
        }

        bool checkRBChildColorInvariant() const 
        {
            if(this->isReprLeaf()) {
                return true;
            }

//----------------------------- 
xxxx;
            if(this->color == RColor::Red) {
                return !(this->left && this->left->color == RColor::Red) && !(this->right && this->right->color == RColor::Red);
            }

            return this->left->checkRBChildColorInvariant() && this->right->checkRBChildColorInvariant();
        }

        static bool checkRBInvariants(const PosRBTree<T, K, TreeID>& tree)
        {
            return checkRBChildColorInvariant(tree.repr) && checkRBPathLengthInvariant(tree.repr) >= 0;
        }
#endif
        
        void debugAssertInvariants() const
        {
#if BSQ_POSTREE_VALIDATE
            assert(checkRBInvariants(this->repr));
#endif
        }

    public:
    };

    template<typename T, int64_t K> 
    consteval TypeInfo g_typeinfo_PosRBTreeNode_generate(uint32_t tid, uint16_t tslots, const char* mask, const char* tname)
    {
        return TypeInfo{
            tid,
            sizeof(PosRBTreeNode<T, K>),
            byteSizeToSlotCount(sizeof(PosRBTreeNode<T, K>)),
            LayoutTag::Ref,
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

    ////
    //Note that we tag each template to keep the types distinct because we have the static allocator/type info! 
    //For now we probably want to mostly PIMPL the persistent tree logic and keep wrappers in the class to avoid code bloat but we can always change this later.
    ////
    template<typename T, int64_t K, uint32_t TreeID>
    class PosRBTree
    {
    public:
        PosRBTreeNode<T, K>* root;

        static const TypeInfo* s_nodetypeinfo;
        thread_local static GCAllocator<PosRBTreeNode<T, K>>* s_nodeallocator;

        PosRBTree() = default;
        PosRBTree(const PosRBTree& other) = default;
        PosRBTree(PosRBTreeNode<T, K>* node) : root(node) { ; }

        // double red violation on the LL side (tleft = Node{_, Red, Node{_, Red, a, b}, c})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_LL(const PosRBTreeRepr<T, K>& cur)
        {
            if(!validateBlackNode(cur)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l  = cur.data.node->left;
            if(!validateRedNode(l)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& ll = l.data.node->left;
            if(!validateRedNode(ll)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& lll = ll.data.node->left;
            const PosRBTreeRepr<T, K>& llr = ll.data.node->right;
            const PosRBTreeRepr<T, K>& lr  = l.data.node->right;
            const PosRBTreeRepr<T, K>& r   = cur.data.node->right;
            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, lll, llr);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, lr, r);
            return makeNode(RColor::Red, nl, nr);
        }

        // double red violation on the LR side (tleft = Node{_, Red, a, Node{_, Red, b, c}})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_LR(const PosRBTreeRepr<T, K>& cur)
        {
            if(!validateBlackNode(cur)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l  = cur.data.node->left;
            if(!validateRedNode(l)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& lr = l.data.node->right;
            if(!validateRedNode(lr)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& ll  = l.data.node->left;
            const PosRBTreeRepr<T, K>& lrl = lr.data.node->left;
            const PosRBTreeRepr<T, K>& lrr = lr.data.node->right;
            const PosRBTreeRepr<T, K>& r   = cur.data.node->right;
            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, ll, lrl);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, lrr, r);
            return makeNode(RColor::Red, nl, nr);
        }

        // double red violation on the RL side (tright = Node{_, Red, Node{_, Red, b, c}, d})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_RL(const PosRBTreeRepr<T, K>& cur)
        {
            if(!validateBlackNode(cur)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& r  = cur.data.node->right;
            if(!validateRedNode(r)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& rl = r.data.node->left;
            if(!validateRedNode(rl)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l   = cur.data.node->left;
            const PosRBTreeRepr<T, K>& rll = rl.data.node->left;
            const PosRBTreeRepr<T, K>& rlr = rl.data.node->right;
            const PosRBTreeRepr<T, K>& rr  = r.data.node->right;
            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, l, rll);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, rlr, rr);
            return makeNode(RColor::Red, nl, nr);
        }

        // double red violation on the RR side (tright = Node{_, Red, b, Node{_, Red, c, d}})
        static std::optional<PosRBTreeRepr<T, K>> balancehelper_RR_RR(const PosRBTreeRepr<T, K>& cur)
        {
            if(!validateBlackNode(cur)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& r  = cur.data.node->right;
            if(!validateRedNode(r)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& rr = r.data.node->right;
            if(!validateRedNode(rr)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l   = cur.data.node->left;
            const PosRBTreeRepr<T, K>& rl  = r.data.node->left;
            const PosRBTreeRepr<T, K>& rrl = rr.data.node->left;
            const PosRBTreeRepr<T, K>& rrr = rr.data.node->right;
            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, l, rl);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, rrl, rrr);
            return makeNode(RColor::Red, nl, nr);
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
                const int64_t lcount = reprcount(cur.data.node->left);
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
                    return makeLeaf(cur.data.leaf->insert(index, value));
                }
                else {
                    constexpr int64_t midpt = K / 2;
                    PosRBTreeLeaf<T, K> nlleaf, nrleaf;
                    if(index < midpt) {
                        nlleaf = cur.data.leaf->subsetinsert(0, index, midpt, value);
                        nrleaf = cur.data.leaf->subset(midpt, K - midpt);
                    }
                    else {
                        nlleaf = cur.data.leaf->subset(0, midpt);
                        nrleaf = cur.data.leaf->subsetinsert(midpt, index, K - midpt, value);
                    }

                    return makeNode(RColor::Red, makeLeaf(nlleaf), makeLeaf(nrleaf)); 
                }
            }
            else {
                PosRBTreeRepr<T, K> nl, nr;
                const int64_t lcount = reprcount(cur.data.node->left);
                if(index < lcount) {
                    nl = inserthelper(index, value, cur.data.node->left);
                    nr = cur.data.node->right;
                }
                else {
                    nl = cur.data.node->left;
                    nr = inserthelper(index - lcount, value, cur.data.node->right); 
                }

                return balance(makeNode(cur.data.node->color, nl, nr));
            }
        }

        PosRBTree<T, K, TreeID> insert(int64_t index, const T& value) const
        {
            PosRBTree<T, K, TreeID> res(inserthelper(index, value, this->repr)); 
            if(res.repr.typeinfo == s_nodetypeinfo) {  
                res.repr.data.node->color = RColor::Black;
                res = PosRBTree<T, K, TreeID>(balance(res.repr));
            }

            debugAssertInvariants(res.repr);
            return res;
        }

        static DeleteResult blackenprime(const PosRBTreeRepr<T, K>& cur)
        {
            if(validateRedNode(cur)) {
                return mkDeleteDone(makeNode(RColor::Black, cur.data.node->left, cur.data.node->right));
            }

            return mkDeleteShort(cur);
        }

        static std::optional<PosRBTreeRepr<T, K>> balanceprimehelper_LL(const PosRBTreeRepr<T, K>& cur)
        {
            if(cur.typeinfo != s_nodetypeinfo) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l = cur.data.node->left;
            if(!validateRedNode(l)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& ll = l.data.node->left;
            if(!validateRedNode(ll)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, ll.data.node->left, ll.data.node->right);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, l.data.node->right, cur.data.node->right);
            return makeNode(cur.data.node->color, nl, nr);
        }

        static std::optional<PosRBTreeRepr<T, K>> balanceprimehelper_LR(const PosRBTreeRepr<T, K>& cur)
        {
            if(cur.typeinfo != s_nodetypeinfo) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& l = cur.data.node->left;
            if(!validateRedNode(l)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& lr = l.data.node->right;
            if(!validateRedNode(lr)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, l.data.node->left, lr.data.node->left);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, lr.data.node->right, cur.data.node->right);
            return makeNode(cur.data.node->color, nl, nr);
        }

        static std::optional<PosRBTreeRepr<T, K>> balanceprimehelper_RL(const PosRBTreeRepr<T, K>& cur)
        {
            if(cur.typeinfo != s_nodetypeinfo) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& r = cur.data.node->right;
            if(!validateRedNode(r)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& rl = r.data.node->left;
            if(!validateRedNode(rl)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, cur.data.node->left, rl.data.node->left);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, rl.data.node->right, r.data.node->right);
            return makeNode(cur.data.node->color, nl, nr);
        }

        static std::optional<PosRBTreeRepr<T, K>> balanceprimehelper_RR(const PosRBTreeRepr<T, K>& cur)
        {
            if(cur.typeinfo != s_nodetypeinfo) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& r = cur.data.node->right;
            if(!validateRedNode(r)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K>& rr = r.data.node->right;
            if(!validateRedNode(rr)) {
                return std::nullopt;
            }

            const PosRBTreeRepr<T, K> nl = makeNode(RColor::Black, cur.data.node->left, r.data.node->left);
            const PosRBTreeRepr<T, K> nr = makeNode(RColor::Black, rr.data.node->left, rr.data.node->right);
            return makeNode(cur.data.node->color, nl, nr);
        }

        static DeleteResult balanceprime(const PosRBTreeRepr<T, K>& cur)
        {
            if(auto res = balanceprimehelper_LL(cur)) {
                return mkDeleteDone(*res);
            }
            else if(auto res = balanceprimehelper_LR(cur)) {
                return mkDeleteDone(*res);
            }
            else if(auto res = balanceprimehelper_RL(cur)) {
                return mkDeleteDone(*res);
            }
            else if(auto res = balanceprimehelper_RR(cur)) {
                return mkDeleteDone(*res);
            }
            else {
                return blackenprime(cur);
            }
        }

        static DeleteResult eqLeft(const PosRBTreeRepr<T, K>& cur)
        {
            assert(cur.typeinfo == s_nodetypeinfo);

            const PosRBTreeRepr<T, K>& r = cur.data.node->right;
            if(validateBlackNode(r)) {
                return balanceprime(makeNode(cur.data.node->color, cur.data.node->left, makeNode(RColor::Red, r.data.node->left, r.data.node->right)));
            }

            assert(validateRedNode(r));
            return mapDeleteResult(eqLeft(makeNode(RColor::Red, cur.data.node->left, r.data.node->left)), [&r](const PosRBTreeRepr<T, K>& a) {
                return makeNode(RColor::Black, a, r.data.node->right);
            });
        }

        static DeleteResult eqRight(const PosRBTreeRepr<T, K>& cur)
        {
            assert(cur.typeinfo == s_nodetypeinfo);

            const PosRBTreeRepr<T, K>& l = cur.data.node->left;
            if(validateBlackNode(l)) {
                return balanceprime(makeNode(cur.data.node->color, makeNode(RColor::Red, l.data.node->left, l.data.node->right), cur.data.node->right));
            }

            assert(validateRedNode(l));
            return mapDeleteResult(eqRight(makeNode(RColor::Red, l.data.node->right, cur.data.node->right)), [&l](const PosRBTreeRepr<T, K>& b) {
                return makeNode(RColor::Black, l.data.node->left, b);
            });
        }

        static DeleteResult collapseAfterEmptyLeft(const PosRBTreeRepr<T, K>& cur)
        {
            assert(cur.typeinfo == s_nodetypeinfo);
            assert(isEmpty(cur.data.node->left));
            assert(!isEmpty(cur.data.node->right));

            return (cur.data.node->color == RColor::Red) ? mkDeleteDone(cur.data.node->right) : blackenprime(cur.data.node->right);
        }

        static DeleteResult collapseAfterEmptyRight(const PosRBTreeRepr<T, K>& cur)
        {
            assert(cur.typeinfo == s_nodetypeinfo);
            assert(!isEmpty(cur.data.node->left));
            assert(isEmpty(cur.data.node->right));

            return (cur.data.node->color == RColor::Red) ? mkDeleteDone(cur.data.node->left) : blackenprime(cur.data.node->left);
        }

        static DeleteResult removehelper(int64_t index, const PosRBTreeRepr<T, K>& cur)
        {
            assert(cur.typeinfo != nullptr);

            if(cur.typeinfo == s_leaftypeinfo) {
                assert(index < cur.data.leaf->count);
                if(cur.data.leaf->count == 1) {
                    return mkDeleteDone(PosRBTreeRepr<T, K>());
                }

                return mkDeleteDone(makeLeaf(cur.data.leaf->remove(index)));
            }

            const int64_t lcount = reprcount(cur.data.node->left);
            if(index < lcount) {
                const DeleteResult lres = removehelper(index, cur.data.node->left);
                const PosRBTreeRepr<T, K> rebuilt = makeNode(cur.data.node->color, lres.repr, cur.data.node->right);

                if(isEmpty(lres.repr)) {
                    return collapseAfterEmptyLeft(rebuilt);
                }

                return lres.isShort() ? eqLeft(rebuilt) : mkDeleteDone(rebuilt);
            }

            const DeleteResult rres = removehelper(index - lcount, cur.data.node->right);
            const PosRBTreeRepr<T, K> rebuilt = makeNode(cur.data.node->color, cur.data.node->left, rres.repr);

            if(isEmpty(rres.repr)) {
                return collapseAfterEmptyRight(rebuilt);
            }

            return rres.isShort() ? eqRight(rebuilt) : mkDeleteDone(rebuilt);
        }

        PosRBTree<T, K, TreeID> remove(int64_t index) const
        {
            assert(this->repr.typeinfo != nullptr);
            assert(index >= 0 && index < this->count());

            PosRBTree<T, K, TreeID> res(removehelper(index, this->repr).repr);
            debugAssertInvariants(res.repr);
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

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

        class TreeNodePath
        {
        public:
            int64_t top;
            std::array<PosRBTreeNode*, 42> nodes;

            TreeNodePath() : top(-1) { ; }

            bool empty() const 
            { 
                return this->top == -1; 
            }

            void push(PosRBTreeNode* node) 
            {
                assert(this->top < 41);
                this->nodes[++this->top] = node;
            }

            PosRBTreeNode* pop() 
            {
                assert(this->top >= 0);
                return this->nodes[this->top--];
            }

            PosRBTreeNode* buildToIndex(int64_t index, PosRBTreeNode* root)
            {
                PosRBTreeNode* cur = root;
                int64_t idx = index;
                while(cur != nullptr) {
                    const int64_t lmax = (cur->left != nullptr) ? cur->left->count : 0;
                    const int64_t tmax = lmax + cur->data.count;

                    if(lmax <= idx && idx < tmax) {
                        return cur;
                    }

                    this->push(cur);
                    if(idx < lmax) {
                        cur = cur->left;
                    }
                    else {
                        idx -= tmax;
                        cur = cur->right;
                    }
                }

                assert(false); // index out of bounds
                return nullptr;
            }
        };

        bool isReprLeaf() const { return (this->left == nullptr) & (this->right == nullptr); }
        bool isReprNode() const { return !isReprLeaf(); }

        static RColor getNodeColor(const PosRBTreeNode* node) { return (node != nullptr) ? node->color : RColor::Black; }
        static bool isRedNode(const PosRBTreeNode* node) { return getNodeColor(node) == RColor::Red; }
        static bool isBlackNode(const PosRBTreeNode* node) { return getNodeColor(node) == RColor::Black; }

        static int64_t reprcount(const PosRBTreeNode* node) { return (node != nullptr) ? node->count : 0; }

        PosRBTreeNode() : count(0), left(nullptr), right(nullptr), data(), color(RColor::Black) { ; }
        PosRBTreeNode(const PosRBTreeNode& other) = default;

        PosRBTreeNode(PosRBTreeNode* left, PosRBTreeNode* right, const PosRBTreeData<T, K>& data, RColor color) : count(reprcount(left) + reprcount(right) + data.count), left(left), right(right), data(data), color(color) { ; }

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

            if(this->color == RColor::Red) {
                return !isRedNode(this->left) && !isRedNode(this->right);
            }

            return this->left->checkRBChildColorInvariant() && this->right->checkRBChildColorInvariant();
        }

        bool checkRBInvariants() const
        {
            return checkRBChildColorInvariant(tree.repr) && checkRBPathLengthInvariant(tree.repr) >= 0;
        }
#endif
        
        void debugAssertInvariants() const
        {
#if BSQ_POSTREE_VALIDATE
            assert(this->checkRBInvariants());
#endif
        }

        // double red violation on the LL side  (B (R (R a x b) y c) z d) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_LL(const PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
        {
            const PosRBTreeNode* l  = cur->left;
            if(!isRedNode(l)) {
                return false;
            }

            const PosRBTreeNode* ll = l->left;
            if(!isRedNode(ll)) {
                return false;
            }

            res = InsertResult::makeTree(
                allocator.allocate(RColor::Red, 
                    allocator.allocate(RColor::Black, ll->left, ll->right, ll->data), 
                    allocator.allocate(RColor::Black, l->right, cur->right, cur->data),
                    l->data
                )
            );
            return true;
        }

        // double red violation on the LR side  (B (R a x (R b y c)) z d) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_LR(const PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
        {
            const PosRBTreeNode* l  = cur->left;
            if(!isRedNode(l)) {
                return false;
            }

            const PosRBTreeNode* lr = l->right;
            if(!isRedNode(lr)) {
                return false;
            }

            res = InsertResult::makeTree(
                allocator.allocate(RColor::Red, 
                    allocator.allocate(RColor::Black, l->left, lr->left, l->data), 
                    allocator.allocate(RColor::Black, lr->right, cur->right, cur->data),
                    lr->data
                )
            );
            return true;
        }

        // double red violation on the RL side  (B a x (R (R b y c) z d)) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_RL(const PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
        {
            const PosRBTreeNode* r  = cur->right;
            if(!isRedNode(r)) {
                return false;
            }

            const PosRBTreeNode* rr = r->right;
            if(!isRedNode(rr)) {
                return false;
            }

            res = InsertResult::makeTree(
                allocator.allocate(RColor::Red, 
                    allocator.allocate(RColor::Black, cur->left, rr->left, cur->data), 
                    allocator.allocate(RColor::Black, rr->right, r->right, r->data),
                    rr->data
                )
            );
            return true;
        }

        // double red violation on the RR side balance (B a x (R b y (R c z d))) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_RR(const PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
        {
            const PosRBTreeNode* r  = cur->right;
            if(!isRedNode(r)) {
                return false;
            }

            const PosRBTreeNode* rr = r->right;
            if(!isRedNode(rr)) {
                return false;
            }

            res = InsertResult::makeTree(
                allocator.allocate(RColor::Red, 
                    allocator.allocate(RColor::Black, cur->left, r->left, cur->data), 
                    allocator.allocate(RColor::Black, rr->left, rr->right, rr->data),
                    r->data
                )
            );
            return true;
        }

        // Just roll up the black nodes -- balance (B a x b) = D (B a x b)
        static bool balancehelper_S_B(PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
        {
            if(isBlackNode(cur)) {
                return false;
            }
xxxx;
            res = InsertResult::makeDone(cur);
            return true;
        }

        // Tentatively roll up the red nodes -- balance (R a x b) = D (R a x b)
        static bool balancehelper_S_R(PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
        {
            if(isRedNode(cur)) {
                return false;
            }
xxxx;
            res = InsertResult::makeTree(curr);
            return true;
        }

        static InsertResult balance(PosRBTreeNode* cur, GCAllocator<PosRBTreeNode>& allocator)
        {
            InsertResult res;
            if(balancehelper_RR_LL(cur, res, allocator)) {
                return res;
            }
            else if(balancehelper_RR_LR(cur, res, allocator)) {
                return res;
            }
            else if(balancehelper_RR_RL(cur, res, allocator)) {
                return res;
            }
            else if(balancehelper_RR_RR(cur, res, allocator)) {
                return res;
            }
            else if(balancehelper_S_B(cur, res, allocator)) {
                return res;
            }
            else {
                balancehelper_S_R(cur, res, allocator);
                return res;
            }   
        }

        static PosRBTree* copyNodeForSpine(PosRBTreeNode* node, xxxx, GCAllocator<PosRBTreeNode>& allocator)
        {
            return allocator.allocate(node->color, node->left, node->right, node->data);
        }

        static PosRBTree* copyNodeForSpineReplace(PosRBTreeNode* node, const PosRBTreeData& ndata, GCAllocator<PosRBTreeNode>& allocator)
        {
            return allocator.allocate(node->color, node->left, node->right, ndata);
        }

        PosRBTreeNode* insert(int64_t index, const T& value, GCAllocator<PosRBTreeNode>& allocator)
        {
            TreeNodePath path;
            PosRBTreeNode* insnode = path.buildToIndex(index, this);

            if(insnode->count < K) {
                xxxx;
                insnode->data = insnode->data.insert(index, value);
                insnode->count++;

                return this;
            }
            else {
                xxxx;
                InsertResult res = balance(insnode->insert(index, value, allocator), allocator);
                if(res.isDone()) {
                    return this;
                }
                else {
                    PosRBTreeNode* newroot = res.tnode;
                    newroot->color = RColor::Black;
                    return newroot;
                }
            }
        }

        /*
        insert :: Ord a => a -> Tree a -> Tree a
insert x s = (blacken . fromResult . ins) s
where ins E = T (R E x E)
ins (N k a y b)
| x < y = balance =<< (\a -> N k a y b) <$$> ins a
| x == y = D (N k a y b)
| x > y = balance =<< (\b -> N k a y b) <$$> ins 
*/
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

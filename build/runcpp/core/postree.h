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

        static zerofill(std::array<T, K>& data, size_t ecount)
        {
            uint8_t* rawdata = reinterpret_cast<uint8_t*>(data.data()); 
            std::fill(rawdata + ecount * sizeof(T), rawdata + K * sizeof(T), 0);
        }

        PosRBTreeData() : count(0) 
        {
            zerofill(this->data, 0);
        }

        PosRBTreeData(const PosRBTreeData& other) = default;

        /** Constructor when we have a range of values that follow  **/
        template<typename Iter>
        PosRBTreeData(Iter start, Iter end)
        {            
            const int64_t size = std::distance(start, end);
            assert(size != 0);
            assert(size <= K);

            std::copy(start, end, this->data.begin());
            zerofill(this->data, size);
            this->count = size; 
        }

        /** Constructor when we have a single value at position 0 and a range of values that follow -- pushFront style constructor  **/
        template<typename Iter, bool isfull>
        PosRBTreeData(const T& ival, Iter rstart, Iter rend)
        {   
            assert(1 + std::distance(rstart, rend) <= K);    
            assert(!isfull || (1 + std::distance(rstart, rend) == K));

            this->data[0] = ival;
            std::copy(rstart, rend, this->data.begin() + 1);

            if constexpr (isfull) {
                this->count = K;
            }
            else {
                this->count = 1 + std::distance(rstart, rend);
                zerofill(this->data, this->count);
            }
        }

        /** Constructor when we have a range of values and a single value at the end -- pushBack style constructor  **/
        template<typename Iter, bool isfull>
        PosRBTreeData(Iter lstart, Iter lend, const T& ival)
        {          
            assert(1 + std::distance(lstart, lend) <= K);  
            assert(!isfull || (std::distance(lstart, lend) + 1 == K));

            std::copy(lstart, lend, this->data.begin());
            this->data[std::distance(lstart, lend)] = ival;

            if constexpr (isfull) {
                this->count = K;
            }
            else {
                this->count = std::distance(lstart, lend) + 1;
                zerofill(this->data, this->count);
            }
        }

        /** Constructor when we have a range of values, a single value, and then another range of values -- insert middle style constructor  **/
        template<typename Iter, bool isfull>
        PosRBTreeData(Iter lstart, Iter lend, const T& ival, Iter rstart, Iter rend)
        {
            assert(std::distance(lstart, lend) + 1 + std::distance(rstart, rend) <= K);
            assert(!isfull || (std::distance(lstart, lend) + 1 + std::distance(rstart, rend) == K));

            std::copy(lstart, lend, this->data.begin());
            this->data[std::distance(lstart, lend)] = ival;
            std::copy(rstart, rend, this->data.begin() + std::distance(lstart, lend) + 1);

            if constexpr (isfull) {
                this->count = K;
            }
            else {
                this->count = std::distance(lstart, lend) + 1 + std::distance(rstart, rend);
                zerofill(this->data, this->count);
            }
        }

        PosRBTreeData(std::initializer_list<T> args)
        {
            assert(args.size() != 0);
            assert(args.size() <= K);

            std::copy(args.begin(), args.end(), this->data.begin());
            zerofill(this->data, args.size());
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
            assert((0 < index) & (index < K));
            assert(this->count < K);

            xxxx;
            if(index == 0) {
                return PosRBTreeData(std::initializer_list<T>{value}, this->data.cbegin(), this->data.cbegin() + this->count);
            }
            else if(index == this->count) {
                PosRBTreeData nleaf;
                std::copy(this->data.cbegin(), this->data.cbegin() + this->count, nleaf.data.begin());
                nleaf.data[this->count] = value;
                nleaf.count = this->count + 1;

                return nleaf;
            }
            PosRBTreeData nleaf;
            if(0 < index) {
                std::copy(this->data.cbegin(), this->data.cbegin() + index, nleaf.data.begin());
            }

            if(index < this->count) {
                std::copy(this->data.cbegin() + index, this->data.cbegin() + this->count, nleaf.data.begin() + index + 1);               
            }

            nleaf.data[index] = value;
            nleaf.count = this->count + 1;

            return nleaf;
        }

        PosRBTreeData insertSpillLeft(int64_t index, const T& value, T& spill) const
        {
            assert((0 <= index) & (index < K));
            assert(this->count == K);
          
            if(index == 0) {
                spill = value;
                return *this;
            }
            else {
                spill = this->data.front();

                PosRBTreeData nleaf;
                std::copy(this->data.cbegin() + 1, this->data.cbegin() + index, nleaf.data.begin());
                std::copy(this->data.cbegin() + index + 1, this->data.cend(), nleaf.data.begin() + index + 1);               
                
                nleaf.data[index] = value;
                nleaf.count = K;

                return nleaf;
            }
        }

        PosRBTreeData insertSpillRight(int64_t index, const T& value, T& spill) const
        {
            assert((0 < index) & (index <= K));
            assert(this->count == K);
          
            if(index == K) {
                spill = value;
                return *this;
            }
            else {
                spill = this->data.back();

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

            template<typename Fn>
            InsertResult apply(Fn fn) const
            {
                return InsertResult{this->tag, fn(this->tnode)};
            }
        };

        enum class DeleteResultTag
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

        enum class PathDirection
        {
            Left,
            Right
        };

        class TreeNodePath
        {
        public:
            int64_t top;
            std::array<std::pair<PathDirection, PosRBTreeNode*>, 32> nodes;

            TreeNodePath() : top(-1) { ; }

            bool empty() const 
            { 
                return this->top == -1; 
            }

            void push(PathDirection direction, PosRBTreeNode* node) 
            {
                assert(this->top < 31);
                this->nodes[++this->top] = std::make_pair(direction, node);
            }

            std::pair<PathDirection, PosRBTreeNode*> pop() 
            {
                assert(this->top >= 0);
                return this->nodes[this->top--];
            }

            //Must check index bounds before calling this function! -- range can be [0, count] where (inclusive) count is the "one past the end" index
            std::pair<PosRBTreeNode*, int64_t> buildToIndex(int64_t index, PosRBTreeNode* root)
            {
                PosRBTreeNode* cur = root;
                int64_t idx = index;
                while(true) {
                    const int64_t lmax = (cur->left != nullptr) ? cur->left->count : 0;
                    const int64_t tmax = lmax + cur->data.count ((cur->right != nullptr) ? 0 : 1); //if we have no right child but index is 1 past end, then we are the node to insert (or look) at

                    if(lmax <= idx && idx < tmax) {
                        return std::make_pair(cur, idx - lmax);
                    }

                    if(idx < lmax) {
                        this->push(PathDirection::Left, cur);
                        cur = cur->left;
                    }
                    else {
                        idx -= tmax;

                        this->push(PathDirection::Right, cur);
                        cur = cur->right;
                    }
                }
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
        static bool balancehelper_RR_LL(PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
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
        static bool balancehelper_RR_LR(PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
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
        static bool balancehelper_RR_RL(PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
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
        static bool balancehelper_RR_RR(PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
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

            res = InsertResult::makeDone(cur);
            return true;
        }

        // Tentatively roll up the red nodes -- balance (R a x b) = T (R a x b)
        static bool balancehelper_S_R(PosRBTreeNode* cur, InsertResult& res, GCAllocator<PosRBTreeNode>& allocator)
        {
            if(isRedNode(cur)) {
                return false;
            }

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

        static PosRBTree* copyNodeSpine(const std::pair<PathDirection, PosRBTreeNode*>& nodepath, PosRBTreeNode* curr, GCAllocator<PosRBTreeNode>& allocator)
        {
            PosRBTreeNode* nl = nodepath.first == PathDirection::Left ? curr : nodepath.second->left;
            PosRBTreeNode* nr = nodepath.first == PathDirection::Right ? curr : nodepath.second->right;

            return allocator.allocate(nodepath.second->color, nl, nr, nodepath.second->data);
        }

        static PosRBTree* copyNodeReplaceData(PosRBTreeNode* node, const PosRBTreeData& ndata, GCAllocator<PosRBTreeNode>& allocator)
        {
            return allocator.allocate(node->color, node->left, node->right, ndata);
        }

        static PosRBTreeNode* insert_spill(PosRBTreeNode* node, int64_t index, const T& value, GCAllocator<PosRBTreeNode>& allocator)
        {
            if(node == nullptr) {
                return allocator.allocate(RColor::Red, nullptr, nullptr, PosRBTreeData<T, K>{value});
            }


        }

        PosRBTreeNode* insert(int64_t index, const T& value, GCAllocator<PosRBTreeNode>& allocator)
        {
            TreeNodePath path;
            PosRBTreeNode* opnode = path.buildToIndex(index, this);

            if(opnode->count < K) {
                //we can add the element without modifying structure -- no rebalancing needed just copy spine
                PosRBTreeNode* curr = copyNodeReplaceData(opnode, opnode->data.insert(index, value), allocator);
                while(!path.empty()) {
                    curr = copyNodeSpine(path.pop(), curr, allocator);
                }

                return blacken(curr);
            }
            else {
                // we need to split the leaf and add a new node -- must do rebalance
                InsertResult res;
                if(index == 0) {
                    //then spill the insert element down to the left
                    xxxx;
                }
                else if(index == K) { 
                    //then spill the insert element down to the right
                    xxxx;
                }
                else if(opnode->left == nullptr) {
                    //create a new leaf
                    if(opnode->left == nullptr) {
                        xxxx;
                    }
                    else {
                        xxxx;
                    }
                }
                else {
                    //evict an element down the tree
                    
                    else {
                        if(opnode->left->count < opnode->right->count) {
                             //evict to left
                            int64_t lshiftidx = xxxx;
                            PosRBTreeNode* nleft = insert(lshiftidx, opnode->data.front(), allocator);
                        
                            xxxx;
                            PosRBTreeNode* inode = allocator.allocate(opnode->color, left, opnode->right, xxx);
                            res = InsertResult::makeTree(inode);
                        }
                        else {
                            //evict to right
                            int64_t rshiftidx = xxxx;
                            PosRBTreeNode* nright = insert(rshiftidx, opnode->data.back(), allocator);

                            xxxx;
                            PosRBTreeNode* inode = allocator.allocate(opnode->color, opnode->left, nright, xxx);
                            res = InsertResult::makeTree(inode);
                        }
                    }
                }

                //now rebalance the tree on the way up
                while(path.empty()) {
                    xxxx;
                }

                return blacken(res.tnode);
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

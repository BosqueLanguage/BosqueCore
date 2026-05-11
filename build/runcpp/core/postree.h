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
    enum class RColor : uint16_t
    {
        Red,
        Black
    };
    
    template<typename T, size_t K>
    class PosRBData
    {
    public:
        RColor color;
        uint16_t bheight; //black height of the subtree rooted at this node

        int32_t dcount; //note that when the color follows immediately in enclosing classes the alignment works
        T data[K];

        static void zerofill(T* data, size_t ecount)
        {
            uint8_t* rawdata = reinterpret_cast<uint8_t*>(data); 
            std::fill(rawdata + ecount * sizeof(T), rawdata + K * sizeof(T), 0);
        }

        PosRBData() : color(RColor::Black), bheight(0), dcount(0), data()
        {
            zerofill(this->data, 0);
        }

        PosRBData(const PosRBData& other) : color(other.color), bheight(other.bheight), dcount(other.dcount)
        {
            std::copy(other.data, other.data + K, this->data);
        }

        PosRBData(RColor color, uint16_t bheight, const T& value) : color(color), bheight(bheight), dcount(1)
        {
            this->data[0] = value;
            zerofill(this->data, 1);
        }

        PosRBData(RColor color, uint16_t bheight, const PosRBData<T, K>& data) : color(color), bheight(bheight), dcount(data.dcount)
        {
            std::copy(data.data, data.data + K, this->data);
        }

        /** Constructor when we have a range of values  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter start, Iter end) : color(color), bheight(bheight)
        {            
            const int64_t size = std::distance(start, end);
            assert(size != 0);
            assert(size <= K);

            std::copy(start, end, this->data);
            zerofill(this->data, size);
            this->dcount = size; 
        }

        /** Constructor when we have a single value at position 0 and a range of values that follow -- pushFront style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, const T& ival, Iter rstart, Iter rend) : color(color), bheight(bheight)
        {   
            assert(1 + std::distance(rstart, rend) <= K);

            this->data[0] = ival;
            std::copy(rstart, rend, this->data + 1);
            this->dcount = 1 + std::distance(rstart, rend);

            if(this->dcount < K) {
                zerofill(this->data, this->dcount);
            }
        }

        /** Constructor when we have a range of values and a single value at the end -- pushBack style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter lstart, Iter lend, const T& ival) : color(color), bheight(bheight)
        {          
            assert(1 + std::distance(lstart, lend) <= K);

            std::copy(lstart, lend, this->data);
            this->data[std::distance(lstart, lend)] = ival;
            this->dcount = std::distance(lstart, lend) + 1;

            if(this->dcount < K) {
                zerofill(this->data, this->dcount);
            }
        }

        /** Constructor when we have a range of values, a single value, and then another range of values -- insert middle style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter lstart, Iter lend, const T& ival, Iter rstart, Iter rend) : color(color), bheight(bheight)
        {
            assert(std::distance(lstart, lend) + 1 + std::distance(rstart, rend) <= K);

            std::copy(lstart, lend, this->data);
            this->data[std::distance(lstart, lend)] = ival;
            std::copy(rstart, rend, this->data + std::distance(lstart, lend) + 1);
            this->dcount = std::distance(lstart, lend) + 1 + std::distance(rstart, rend);

            if(this->dcount < K) {
                zerofill(this->data, this->dcount);
            }
        }

        /** Constructor when we have a range of values and then another range of values -- remove middle style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter lstart, Iter lend, Iter rstart, Iter rend) : color(color), bheight(bheight)
        {
            std::copy(lstart, lend, this->data);
            std::copy(rstart, rend, this->data + std::distance(lstart, lend));
            this->dcount = std::distance(lstart, lend) + std::distance(rstart, rend);

            zerofill(this->data, this->dcount);
        }

        PosRBData pushfront(const T& value) const
        {
            assert(this->dcount < K);
            return PosRBData(this->color, this->bheight, value, this->data, this->data + this->dcount);
        }

        PosRBData pushback(const T& value) const
        {
            assert(this->dcount < K);
            return PosRBData(this->color, this->bheight, this->data, this->data + this->dcount, value);
        }

        PosRBData insert(int64_t index, const T& value) const
        {
            assert((0 <= index) & (index <= this->dcount));
            assert(this->dcount < K);

            if(index == 0) {
                return PosRBData(this->color, this->bheight, value, this->data, this->data + this->dcount);
            }
            else if(index == this->dcount) {
                return PosRBData(this->color, this->bheight, this->data, this->data + this->dcount, value);
            }
            else {
                return PosRBData(this->color, this->bheight, this->data, this->data + index, value, this->data + index, this->data + this->dcount);
            }
        }

        PosRBData insertSpillLeft(int64_t index, const T& value, T& spill) const
        {
            assert((0 <= index) & (index < K));
            assert(this->dcount == K);
          
            if(index == 0) {
                spill = value;
                return *this;
            }
            else {
                spill = this->data[0];
                return PosRBData(this->color, this->bheight, this->data + 1, this->data + index, value, this->data + index, this->data + K);
            }
        }

        PosRBData insertSpillRight(int64_t index, const T& value, T& spill) const
        {
            assert((0 < index) & (index <= K));
            assert(this->dcount == K);
          
            if(index == K) {
                spill = value;
                return *this;
            }
            else {
                spill = this->data[K - 1];
                return PosRBData(this->color, this->bheight, this->data, this->data + index, value, this->data + index, this->data + K - 1);
            }
        }

        PosRBData remove(int64_t index) const
        {
            assert((0 <= index) & (index < this->dcount));
            assert(this->dcount > 1);

            if(index == 0) {
                return PosRBData(this->color, this->bheight, this->data + 1, this->data + this->dcount);
            }
            else if(index == this->dcount - 1) {
                return PosRBData(this->color, this->bheight, this->data, this->data + this->dcount - 1);
            }
            else {
                return PosRBData(this->color, this->bheight, this->data, this->data + index, this->data + index + 1, this->data + this->dcount);
            }
        }
    };

    template<typename T, size_t K> class PosRBTreeLeaf;
    template<typename T, size_t K> class PosRBTreeNode;

    template<typename T, size_t K>
    class PosRBNode
    {
    public:
        PosRBData<T, K> data;

        PosRBNode() = default;
        PosRBNode(const PosRBNode& other) = default;

        PosRBNode(const PosRBData<T, K>& data) : data(data) { ; }
        PosRBNode(RColor color, uint16_t bheight, const PosRBData<T, K>& data) : data(color, bheight, data) { ; }
    };

    template<typename T, size_t K>
    class PosRBTreeLeaf : public PosRBNode<T, K>
    {
    public:
        PosRBTreeLeaf() : PosRBNode<T, K>() = default;
        PosRBTreeLeaf(const PosRBTreeLeaf& other) = default;
        
        PosRBTreeNode(RColor color, const PosRBData<T, K>& data) : PosRBNode<T, K>(color, color == RColor::Black ? 1 : 0, data)
        {
            ;
        }
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
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            tname
        };
    }

    template<typename T, size_t K> 
    class PosRBTreeNode : public PosRBNode<T, K>
    {
    public:
        PosRBNode* left;
        PosRBNode* right;
        int64_t tcount; //total number of elements in the subtree rooted at this node

        PosRBTreeNode() = default;
        PosRBTreeNode(const PosRBTreeNode& other) = default;

        PosRBTreeNode(RColor color, uint16_t bheight, int64_t tcount, PosRBNode* left, PosRBNode* right, const PosRBData<T, K>& data) : PosRBNode<T, K>(color, bheight, data), left(left), right(right), tcount(tcount)
        {
            ;
        }
    };

    template<typename T, size_t K> 
    consteval TypeInfo g_typeinfo_PosRBTreeNode_generate(uint32_t tid, const char* mask, const char* tname)
    {
        return TypeInfo{
            tid,
            sizeof(PosRBTreeNode<T, K>),
            byteSizeToSlotCount(sizeof(PosRBTreeNode<T, K>)),
            LayoutTag::Ref,
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
    template<typename T, size_t K, uint32_t TreeID>
    class PosRBTree
    {
    public:
        PosRBNode<T, K>* root;

        static const TypeInfo* s_leaftypeinfo;
        thread_local static GCAllocator<PosRBTreeLeaf<T, K>>* s_leafallocator;

        static const TypeInfo* s_nodetypeinfo;
        thread_local static GCAllocator<PosRBTreeNode<T, K>>* s_nodeallocator;

        PosRBTree() = default;
        PosRBTree(const PosRBTree& other) = default;
        PosRBTree(PosRBNode<T, K>* node) : root(node) { ; }

        constexpr static bool isLeafType(const PosRBNode<T, K>* node) { return (node != nullptr) && (gcGetTypeInfo(node) == s_leaftypeinfo); }
        constexpr static bool isNodeType(const PosRBNode<T, K>* node) { return (node != nullptr) && (gcGetTypeInfo(node) == s_nodetypeinfo); }

        constexpr static const PosRBTreeLeaf<T, K>* asLeafType(const PosRBNode<T, K>* node) { return static_cast<const PosRBTreeLeaf<T, K>*>(node); }
        constexpr static const PosRBTreeNode<T, K>* asNodeType(const PosRBNode<T, K>* node) { return static_cast<const PosRBTreeNode<T, K>*>(node); }

        constexpr static int64_t reprGetBHeight(const PosRBNode<T, K>* node)
        {
            return (node != nullptr) ? node->data.bheight : 0;
        }

        constexpr static int64_t reprGetCount(const PosRBNode<T, K>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            else {
                return (isLeafType(node)) ? node->data.dcount : asNodeType(node)->tcount;
            }
        }

        constexpr static PosRBNode<T, K>* reprGetLeft(PosRBNode<T, K>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->left : nullptr;
        }

        constexpr static PosRBNode<T, K>* reprGetRight(PosRBNode<T, K>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->right : nullptr;
        }

        constexpr static PosRBNode<T, K>* mknode(RColor color, PosRBNode<T, K>* left, PosRBNode<T, K>* right, const PosRBTreeData<T, K>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator->allocate(color, data);
            }
            else {
                return s_nodeallocator.allocate(color, reprGetBHeight(left), reprGetCount(left) + reprGetCount(right) + data.dcount, left, right, data);
            }
        }

        constexpr static PosRBNode<T, K>* copyNodeReplaceData(PosRBNode<T, K>* node, const PosRBTreeData& ndata)
        {
            if(isLeafType(node)) {
                return s_leafallocator.allocate(node->color, ndata);
            }  
            else {
                return s_nodeallocator.allocate(node->color, reprGetBHeight(node->left), reprGetCount(node->left) + reprGetCount(node->right) + ndata.dcount, node->left, node->right, ndata);
            }
        }

        constexpr static PosRBNode<T, K>* mkcopynode(RColor color, PosRBNode<T, K>* left, PosRBNode<T, K>* right, const PosRBTreeData<T, K>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator.allocate(color, data);
            }
            else {
                return s_nodeallocator.allocate(color, reprGetBHeight(left), reprGetCount(left) + reprGetCount(right) + data.dcount, left, right, data);
            }
        }

        static PosRBNode<T, K>* reprGetMinNode(PosRBNode<T, K>* curr)
        {
            while(reprGetLeft(curr) != nullptr) {
                curr = reprGetLeft(curr);
            }
            return curr;
        }

        static PosRBNode<T, K>* reprGetMaxNode(PosRBNode<T, K>* curr)
        {
            while(reprGetRight(curr) != nullptr) {
                curr = reprGetRight(curr);
            }
            return curr;
        }

        static PosRBNode<T, K>* reprGetIndexNode(int64_t index, PosRBNode<T, K>* curr)
        {
            while(true) {
                int64_t lcount = reprGetCount(curr);

                if(index < lcount) {
                    curr = reprGetLeft(curr);
                }
                else if(lcount + curr->data.dcount <= index) {
                    index -= (lcount + curr->data.dcount);
                    curr = reprGetRight(curr);
                }
                else {
                    return curr; //index is within the current node
                }
            }
        }
        
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
            PosRBNode<T, K>* tnode;

            static InsertResult makeDone(PosRBNode<T, K>* tnode) { return InsertResult{InsertResultTag::Done, tnode}; }
            static InsertResult makeTree(PosRBNode<T, K>* ptree) { return InsertResult{InsertResultTag::Tree, ptree}; }

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
            PosRBNode<T, K>* tnode;

            static DeleteResult makeDone(PosRBNode<T, K>* tnode) { return DeleteResult{DeleteResultTag::Done, tnode}; }
            static DeleteResult makeShort(PosRBNode<T, K>* tnode) { return DeleteResult{DeleteResultTag::Short, tnode}; }

            constexpr bool isDone() const { return this->tag == DeleteResultTag::Done; }
            constexpr bool isShort() const { return this->tag == DeleteResultTag::Short; }
        };

#if BSQ_POSTREE_VALIDATE
        static int64_t checkRBPathLengthInvariant(PosRBNode<T, K>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            
            if(isLeafType(node)) {
                return (node->color == RColor::Black) ? 1 : 0;
            }
            else (isNodeType(node)) {
                PosRBTreeNode<T, K>* tnode = asNodeType(node);
            
                int64_t lc = (tnode->left !== nullptr) ? tnode->left->checkRBPathLengthInvariant() : 0;
                if(lc == -1) {
                    return -1;
                }

                int64_t rc = (tnode->right !== nullptr) ? tnode->right->checkRBPathLengthInvariant() : 0;
                if(rc == -1) {
                    return -1;
                }

                if(lc != rc) { // black height mismatch
                    return -1;
                }

                return (node->color == RColor::Black) ? (lc + 1) : lc;
            }
        }

        static bool checkRBChildColorInvariant(PosRBNode<T, K>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            }

            if(isNodeType(node)) {
                PosRBTreeNode<T, K>* tnode = asNodeType(node);
                
                if(tnode->color == RColor::Red) {
                    if(tnode->left != nullptr && tnode->left->color == RColor::Red) {
                        return false;
                    }
                    if(tnode->right != nullptr && tnode->right->color == RColor::Red) {
                        return false;
                    }
                }

                return tnode->left->checkRBChildColorInvariant() && tnode->right->checkRBChildColorInvariant();
            }
        }

        static bool checkRBLeafInvariant(PosRBNode<T, K>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            }

            if(isNodeType(node)) {
                PosRBTreeNode<T, K>* tnode = asNodeType(node);
                
                if(tnode->left == nullptr && tnode->right != nullptr) {
                    return false;
                }

                return tnode->left->checkRBLeafInvariant() && tnode->right->checkRBLeafInvariant();
            }
        }

        static bool checkRBInvariants(PosRBNode<T, K>* node)
        {
            return checkRBChildColorInvariant(node) && checkRBPathLengthInvariant(node) >= 0 && checkRBLeafInvariant(node);
        }
    #endif
            
        static void debugAssertInvariants(PosRBNode<T, K>* node, int64_t expectedCount)
        {
#if BSQ_POSTREE_VALIDATE
            assert(checkRBInvariants(node));
            assert(reprGetCount(node) == expectedCount);
#endif
        }

        // double red violation on the LL side  (B (R (R a x b) y c) z d) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_LL(PosRBNode<T, K>* cur, InsertResult& res)
        {
            if(cur == nullptr || cur->color != RColor::Black) {
                return false;
            }

            if(isLeafType(cur)) {
                return false;
            }
            else {
                PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBTreeNode* l = reprGetLeft(tnode);
                if(l == nullptr || l->color != RColor::Red) {
                    return false;
                }

                const PosRBTreeNode* ll = reprGetLeft(l);
                if(ll == nullptr || ll->color != RColor::Red) {
                    return false;
                }

                res = InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(ll), reprGetRight(ll), ll->data), 
                        mkcopynode(RColor::Black, reprGetRight(l), reprGetRight(tnode), tnode->data),
                        l->data
                    )
                );
                return true;
            }
        }

        // double red violation on the LR side  (B (R a x (R b y c)) z d) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_LR(PosRBNode<T, K>* cur, InsertResult& res)
        {
            if(cur == nullptr || cur->color != RColor::Black) {
                return false;
            }

            if(isLeafType(cur)) {
                return false;
            }
            else {
                PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBTreeNode* l  = reprGetLeft(tnode);
                if(l == nullptr || l->color != RColor::Red) {
                    return false;
                }

                const PosRBTreeNode* lr = reprGetRight(l);
                if(lr == nullptr || lr->color != RColor::Red) {
                    return false;
                }

                res = InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(l), reprGetLeft(lr), l->data), 
                        mkcopynode(RColor::Black, reprGetRight(lr), reprGetRight(tnode), tnode->data),
                        lr->data
                    )
                );
                return true;
            }
        }

        // double red violation on the RL side  (B a x (R (R b y c) z d)) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_RL(PosRBNode<T, K>* cur, InsertResult& res)
        {
            if(cur == nullptr || cur->color != RColor::Black) {
                return false;
            }

            if(isLeafType(cur)) {
                return false;
            }
            else {
                PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBTreeNode* r = reprGetRight(tnode);
                if(r == nullptr || r->color != RColor::Red) {
                    return false;
                }

                const PosRBTreeNode* rr = reprGetRight(r);
                if(rr == nullptr || rr->color != RColor::Red) {
                    return false;
                }

                res = InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(tnode), reprGetLeft(rr), tnode->data), 
                        mkcopynode(RColor::Black, reprGetRight(rr), reprGetRight(r), r->data),
                        rr->data
                    )
                );
                return true;
            }
        }

        // double red violation on the RR side balance (B a x (R b y (R c z d))) = T (R (B a x b) y (B c z d))
        static bool balancehelper_RR_RR(PosRBNode<T, K>* cur, InsertResult& res)
        {
            if(cur == nullptr || cur->color != RColor::Black) {
                return false;
            }

            if(isLeafType(cur)) {
                return false;
            }
            else {
                PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBTreeNode* r = reprGetRight(tnode);
                if(r == nullptr || r->color != RColor::Red) {
                    return false;
                }

                const PosRBTreeNode* rr = reprGetRight(r);
                if(rr == nullptr || rr->color != RColor::Red) {
                    return false;
                }

                res = InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(tnode), reprGetLeft(r), tnode->data), 
                        mkcopynode(RColor::Black, reprGetLeft(rr), reprGetRight(rr), rr->data),
                        r->data
                    )
                );
                return true;
            }
        }

        // Just roll up the black nodes -- balance (B a x b) = D (B a x b)
        static bool balancehelper_S_B(PosRBNode<T, K>* cur, InsertResult& res)
        {
            if(cur == nullptr || cur->color != RColor::Black) {
                return false;
            }

            res = InsertResult::makeDone(cur);
            return true;
        }

        // Tentatively roll up the red nodes -- balance (R a x b) = T (R a x b)
        static bool balancehelper_S_R(PosRBNode<T, K>* cur, InsertResult& res)
        {
            if(cur == nullptr || cur->color != RColor::Red) {
                return false;
            }

            res = InsertResult::makeTree(curr);
            return true;
        }

        static InsertResult balance(const InsertResult& rres)
        {
            if(rres.isDone()) {
                return rres;
            }

            InsertResult res;
            PosRBNode<T, K>* cur = rres.getTree();
            if(balancehelper_RR_LL(cur, res)) {
                return res;
            }
            else if(balancehelper_RR_LR(cur, res)) {
                return res;
            }
            else if(balancehelper_RR_RL(cur, res)) {
                return res;
            }
            else if(balancehelper_RR_RR(cur, res)) {
                return res;
            }
            else if(balancehelper_S_B(cur, res)) {
                return res;
            }
            else {
                balancehelper_S_R(cur, res);
                return res;
            }   
        }

        static InsertResult pushfrontrec(PosRBNode<T, K>* curr, const T& value)
        {
            //add the element in a new leaf
            if(curr == nullptr) {
                PosRBTreeLeaf<T, K> nleaf = s_leafallocator->allocate(PosRBData<T, K>(RColor::Red, 0, value));
                return InsertResult::makeTree(nleaf);
            }

            //we can add the element without modifying structure -- no rebalancing needed just copy spine
            if(curr->data.dcount < K && reprGetLeft(curr) == nullptr) {
                PosRBNode<T, K>* curr = copyNodeReplaceData(curr, curr->data.pushfront(value));
                return InsertResult::makeDone(curr);
            }
            else {
                InsertResult nleft = pushfrontrec(reprGetLeft(curr), value);
                return balance(nleft.apply([curr](PosRBNode<T, K>* tnode) { return mknode(curr->color, tnode, reprGetRight(curr), curr->data); }));
            }
        }

        static InsertResult pushbackrec(PosRBNode<T, K>* curr, const T& value)
        {
            //add the element in a new leaf
            if(curr == nullptr) {
                PosRBTreeLeaf<T, K> nleaf = s_leafallocator->allocate(PosRBData<T, K>(RColor::Red, 0, value));
                return InsertResult::makeTree(nleaf);
            }

            //we can add the element without modifying structure -- no rebalancing needed just copy spine
            if(curr->data.dcount < K && reprGetRight(curr) == nullptr) {
                PosRBNode<T, K>* curr = copyNodeReplaceData(curr, curr->data.pushback(value));
                return InsertResult::makeDone(curr);
            }
            else {
                InsertResult nright = pushbackrec(reprGetRight(curr), value);
                return balance(nright.apply([curr](PosRBNode<T, K>* tnode) { return mknode(curr->color, reprGetLeft(curr), tnode, curr->data); }));
            }
        }

        static InsertResult insertrec(PosRBNode<T, K>* curr, int64_t index, const T& value)
        {
            if(curr == nullptr) {
                //add the element in a new leaf
                PosRBTreeLeaf<T, K> nleaf = s_leafallocator->allocate(PosRBData<T, K>(RColor::Red, 0, value));
                return InsertResult::makeTree(nleaf);
            }

            if(isLeafType(curr)) {
                PosRBTreeLeaf<T, K>* leaf = asLeafType(curr);
                
                if(curr->data.dcount < K) {
                    PosRBNode<T, K>* curr = copyNodeReplaceData(curr, curr->data.insert(index, value));
                    return InsertResult::makeDone(curr);
                }
                else {
                    if(index < K / 2) {
                        //then spill the insert element down to the left -- but index of 0 must mean there is no left child
                        T spill;
                        PosRBData<T, K> ndata = curr->data.insertSpillLeft(index, value, spill);
                        PosRBTreeLeaf<T, K> lleaf = s_leafallocator->allocate(PosRBData<T, K>(RColor::Red, 0, spill));
                        return balance(InsertResult::makeTree(mknode(ndata.color, lleaf, nullptr, ndata)));
                    }
                    else {
                        //then spill the insert element down to the right -- but index of K must mean there is no left child
                        T spill;
                        PosRBData<T, K> ndata = curr->data.insertSpillRight(index, value, spill);
                        PosRBTreeLeaf<T, K> rleaf = s_leafallocator->allocate(PosRBData<T, K>(RColor::Red, 0, spill));
                        return balance(InsertResult::makeTree(mknode(ndata.color, nullptr, rleaf, ndata)));
                    }
                }
            }
            else {
                PosRBTreeNode<T, K>* opnode = asNodeType(curr);
                PosRBNode<T, K>* l = opnode->left;
                PosRBNode<T, K>* r = opnode->right;
                
                int64_t lcount = reprGetCount(l);
                if(index < lcount) {
                    //insert to left
                    InsertResult nleft = insertrec(l, index, value);
                    return balance(nleft.apply([opnode, r](PosRBNode<T, K>* tnode) { return mknode(opnode->color, tnode, r, opnode->data); }));

                }
                else if(lcount + K <= index) {
                    //insert to right
                    InsertResult nright = insertrec(r, index - (lcount + K), value);
                    return balance(nright.apply([opnode, l](PosRBNode<T, K>* tnode) { return mknode(opnode->color, l, tnode, opnode->data); }));
                }
                else {
                    const nidx = index - lcount;

                    if(curr->data.dcount < K) {
                        //we can add the element without modifying structure -- no rebalancing needed just copy spine
                        PosRBNode<T, K>* curr = copyNodeReplaceData(curr, curr->data.insert(nidx, value));
                        return InsertResult::makeDone(curr);
                    }
                    else {
                        if(nidx < K / 2) {
                            //then spill the insert element down to the left -- but index of 0 must mean there is no left child
                            T spill;
                            PosRBData<T, K> ndata = curr->data.insertSpillLeft(nidx, value, spill);
                            InsertResult nleft = pushbackrec(l, spill);
                            return balance(nleft.apply([opnode, r](PosRBNode<T, K>* tnode) { return mknode(ndata.color, tnode, r, ndata); }));
                        }
                        else {
                            //then spill the insert element down to the right -- but index of K must mean there is no left child
                            T spill;
                            PosRBData<T, K> ndata = curr->data.insertSpillRight(nidx, value, spill);
                            InsertResult nright = pushfrontrec(r, 0, spill);
                            return balance(nright.apply([opnode, l](PosRBNode<T, K>* tnode) { return mknode(ndata.color, l, tnode, ndata); }));
                        }
                    }
                }
            }
        }

        constexpr blacken(InsertResult rr)
        {
            return mknode(RColor::Black, reprGetLeft(rr.tnode), reprGetRight(rr.tnode), rr.tnode->data);
        }

    public:
        constexpr T getFront() const
        {
            PosRBNode<T, K>* minNode = reprGetMinNode(this->repr);
            return minNode->data.data[0];
        }

        constexpr T getBack() const
        {
            PosRBNode<T, K>* maxNode = reprGetMaxNode(this->repr);
            return maxNode->data.data[maxNode->data.dcount - 1];
        }

        constexpr T get(int64_t index) const
        {
            PosRBNode<T, K>* indexNode = reprGetIndexNode(index, this->repr);
            return indexNode->data.data[index - reprGetCount(reprGetLeft(indexNode))];
        }

        PosRBTree<T, K, TreeID> pushFront(const T& value) const
        {
            PosRBNode<T, K>* root = blacken(pushfrontrec(this->repr, value));

            debugAssertInvariants(root, reprGetCount(root) + 1);
            return PosRBTree<T, K, TreeID>{root};
        }

        PosRBTree<T, K, TreeID> pushBack(const T& value) const
        {
            PosRBNode<T, K>* root = blacken(pushbackrec(this->repr, value));

            debugAssertInvariants(root, reprGetCount(root) + 1);
            return PosRBTree<T, K, TreeID>{root};
        }

        PosRBTree<T, K, TreeID> insert(int64_t index, const T& value) const
        {
            PosRBNode<T, K>* root = blacken(insertrec(this->repr, index, value));

            debugAssertInvariants(root, reprGetCount(root) + 1);
            return PosRBTree<T, K, TreeID>{root};
        }
    };

    template<typename T, size_t K, uint32_t TreeID> 
    consteval TypeInfo g_typeinfo_PosRBTree_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo {
            tid,
            sizeof(PosRBTree<T, K, TreeID>),
            byteSizeToSlotCount(sizeof(PosRBTree<T, K, TreeID>)),
            LayoutTag::Ref,
            "1",
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

#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "integrals.h"

#include "../runtime/allocator/alloc.h"

namespace ᐸRuntimeᐳ
{
    template<typename E>
    class CmpRBData
    {
    public:
        RColor color;
        uint16_t bheight; //black height of the subtree rooted at this node

        int32_t dcount; //note that when the color follows immediately in enclosing classes the alignment works -- currently this is just use as alignment padding
        E entry;

        CmpRBData(): color{}, bheight{}, dcount{}, entry{} { ; }
        CmpRBData(const CmpRBData<E>& other) = default;

        CmpRBData(RColor color, uint16_t bheight, const CmpRBData<E>& data) : color{color}, bheight{bheight}, dcount{1}, entry{data.entry} { ; }
        CmpRBData(RColor color, uint16_t bheight, const E& e) : color{color}, bheight{bheight}, dcount{1}, entry{e} { ; }
    };

    template<typename K, typename E> class CmpRBTreeLeaf;
    template<typename K, typename E> class CmpRBTreeNode;

    template<typename K, typename E>
    class CmpRBNode
    {
    public:
        const CmpRBData<E> data;

        CmpRBNode() : data{} { ; }
        CmpRBNode(const CmpRBNode<K, E>& other) = default;

        CmpRBNode(const CmpRBData<E>& data) : data{data} { ; }
        CmpRBNode(RColor color, uint16_t bheight, const CmpRBData<E>& data) : data{color, bheight, data} { ; }
    };

    template<typename K, typename E>
    class CmpRBTreeLeaf : public CmpRBNode<K, E>
    {
    public:
        CmpRBTreeLeaf() : CmpRBNode<K, E>{} { ; }
        CmpRBTreeLeaf(const CmpRBTreeLeaf& other) = default;

        CmpRBTreeLeaf(const CmpRBData<E>& data) : CmpRBNode<K, E>{data} { ; }
        CmpRBTreeLeaf(RColor color, uint16_t bheight, const CmpRBData<E>& data) : CmpRBNode<K, E>{color, bheight, data} { ; }
    };

    template<typename K, typename E>
    consteval TypeInfo g_typeinfo_CmpRBTreeLeaf_generate(uint32_t tid, const char* mask, const char* tname, bool quickrelease)
    {
        return TypeInfo{
            tid,
            sizeof(CmpRBTreeLeaf<K, E>),
            byteSizeToSlotCount(sizeof(CmpRBTreeLeaf<K, E>)),
            LayoutTag::Ref,
            mask,
            nullptr,
            0,
            nullptr,
            0,
            TypeOpDispatchInfo{},
            tname,
            quickrelease
        };
    }

    template<typename K, typename E> 
    class CmpRBTreeNode : public CmpRBNode<K, E>
    {
    public:
        const CmpRBNode<K, E>* left;
        const CmpRBNode<K, E>* right;
        int64_t tcount; //total number of elements in the subtree rooted at this node

        CmpRBTreeNode() : CmpRBNode<K, E>{}, left{}, right{}, tcount{} { ; }
        CmpRBTreeNode(const CmpRBTreeNode& other) = default;

        CmpRBTreeNode(RColor color, uint16_t bheight, int64_t tcount, const CmpRBNode<K, E>* left, const CmpRBNode<K, E>* right, const CmpRBData<E>& data) : CmpRBNode<K, E>{color, bheight, data}, left{left}, right{right}, tcount{tcount} { ; }
    };

    template<typename K, typename E> 
    consteval TypeInfo g_typeinfo_CmpRBTreeNode_generate(uint32_t tid, const char* mask, const char* tname)
    {
        return TypeInfo{
            tid,
            sizeof(CmpRBTreeNode<K, E>),
            byteSizeToSlotCount(sizeof(CmpRBTreeNode<K, E>)),
            LayoutTag::Ref,
            mask,
            nullptr,
            0,
            nullptr,
            0,
            TypeOpDispatchInfo{},
            tname,
            false
        };
    }

    template<typename K, typename E, uint32_t TreeID>
    class CmpRBTree
    {
    public:
        CmpRBNode<K, E>* root;

        static const TypeInfo* s_leaftypeinfo;
        thread_local static GCAllocator<CmpRBTreeLeaf<K, E>>* s_leafallocator;

        static const TypeInfo* s_nodetypeinfo;
        thread_local static GCAllocator<CmpRBTreeNode<K, E>>* s_nodeallocator;

        CmpRBTree() : root{} { ; }
        CmpRBTree(CmpRBNode<K, E>* node) : root{node} { ; }
        CmpRBTree(const CmpRBTree& other) = default;

        static bool isLeafType(const CmpRBNode<K, E>* node) { return (node != nullptr) && (gcGetTypeInfo(const_cast<CmpRBNode<K, E>*>(node)) == s_leaftypeinfo); }
        static bool isNodeType(const CmpRBNode<K, E>* node) { return (node != nullptr) && (gcGetTypeInfo(const_cast<CmpRBNode<K, E>*>(node)) == s_nodetypeinfo); }

        static const CmpRBTreeLeaf<K, E>* asLeafType(const CmpRBNode<K, E>* node) { return static_cast<const CmpRBTreeLeaf<K, E>*>(node); }
        static const CmpRBTreeNode<K, E>* asNodeType(const CmpRBNode<K, E>* node) { return static_cast<const CmpRBTreeNode<K, E>*>(node); }

        static int64_t reprGetBHeight(const CmpRBNode<K, E>* node)
        {
            return (node != nullptr) ? node->data.bheight : 1;
        }

        static int64_t reprGetCount(const CmpRBNode<K, E>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            else {
                return (isLeafType(node)) ? node->data.dcount : asNodeType(node)->tcount;
            }
        }

        static const CmpRBNode<K, E>* reprGetLeft(const CmpRBNode<K, E>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->left : nullptr;
        }

        static const CmpRBNode<K, E>* reprGetRight(const CmpRBNode<K, E>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->right : nullptr;
        }

        static uint16_t computeNewBHeight_ForTreeLeaf(RColor color) { return 1 + ((color == RColor::Black) ? 1 : 0); }
        static uint16_t computeNewBHeight_ForTreeNode(RColor color, const CmpRBNode<K, E>* left, const CmpRBNode<K, E>* right) { return reprGetBHeight(left) + ((color == RColor::Black) ? 1 : 0); }
        static int64_t computeNewCount_ForTreeNode(const CmpRBNode<K, E>* left, const CmpRBNode<K, E>* right, const CmpRBData<E>& data) { return reprGetCount(left) + reprGetCount(right) + data.dcount; }

        template <typename Iter>
        static CmpRBNode<K, E>* mkinitial(const E& value)
        {
            return s_leafallocator->construct(CmpRBData<E>(RColor::Black, 2, value));
        }

        static CmpRBNode<K, E>* mknode(RColor color, const CmpRBNode<K, E>* left, const CmpRBNode<K, E>* right, const CmpRBData<E>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator->construct(color, computeNewBHeight_ForTreeLeaf(color), data);
            }
            else {
                return s_nodeallocator->construct(color, computeNewBHeight_ForTreeNode(color, left, right), computeNewCount_ForTreeNode(left, right, data), left, right, data);
            }
        }

        static CmpRBNode<K, E>* copyNodeReplaceData(const CmpRBNode<K, E>* node, const CmpRBData<E>& ndata)
        {
            if(isLeafType(node)) {
                return s_leafallocator->construct(node->data.color, computeNewBHeight_ForTreeLeaf(node->data.color), ndata);
            }  
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(node);
                return s_nodeallocator->construct(node->data.color, computeNewBHeight_ForTreeNode(node->data.color, tnode->left, tnode->right), computeNewCount_ForTreeNode(tnode->left, tnode->right, ndata), tnode->left, tnode->right, ndata);
            }
        }

        static CmpRBNode<K, E>* mkcopynode(RColor color, const CmpRBNode<K, E>* left, const CmpRBNode<K, E>* right, const CmpRBData<E>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator->construct(color, computeNewBHeight_ForTreeLeaf(color), data);
            }
            else {
                return s_nodeallocator->construct(color, computeNewBHeight_ForTreeNode(color, left, right), computeNewCount_ForTreeNode(left, right, data), left, right, data);
            }
        }

        static const CmpRBNode<K, E>* reprGetMinNode(const CmpRBNode<K, E>* curr)
        {
            while(reprGetLeft(curr) != nullptr) {
                curr = reprGetLeft(curr);
            }
            return curr;
        }

        static const CmpRBNode<K, E>* reprGetMaxNode(const CmpRBNode<K, E>* curr)
        {
            while(reprGetRight(curr) != nullptr) {
                curr = reprGetRight(curr);
            }
            return curr;
        }

        static E reprGetIndexValue(int64_t index, const CmpRBNode<K, E>* curr)
        {
            while(true) {
                if(isLeafType(curr)) {
                    return curr->data.entry;
                }
                else {
                    const CmpRBTreeNode<K, E>* tnode = asNodeType(curr);
                    int64_t lcount = reprGetCount(tnode->left);

                    if(index < lcount) {
                        curr = tnode->left;
                    }
                    else if(index > lcount) {
                        index -= (lcount + 1);
                        curr = tnode->right;
                    }
                    else {
                        return tnode->data.entry;
                    }
                }
            }
        }

        static const CmpRBNode<K, E>* reprGetKeyNode(const K& key, const CmpRBNode<K, E>* curr)
        {
            while(curr != nullptr) {
                if(key < curr->data.entry.key) {
                    curr = reprGetLeft(curr);
                }
                else if(key > curr->data.entry.key) {
                    curr = reprGetRight(curr);
                }
                else {
                    return curr; //key matches the current node
                }
            }

            return nullptr; //key not found
        }

        static E reprGetKeyValue(const K& key, const CmpRBNode<K, E>* curr)
        {
            while(true) {
                if(key < curr->data.entry.key) {
                    curr = reprGetLeft(curr);
                }
                else if(key > curr->data.entry.key) {
                    curr = reprGetRight(curr);
                }
                else {
                    return curr->data.entry.value; //key matches the current node
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
            const InsertResultTag tag;
            const CmpRBNode<K, E>* tnode;

            static InsertResult makeDone(const CmpRBNode<K, E>* tnode) { return InsertResult{InsertResultTag::Done, tnode}; }
            static InsertResult makeTree(const CmpRBNode<K, E>* ptree) { return InsertResult{InsertResultTag::Tree, ptree}; }

            bool isEmpty() const { return this->tnode == nullptr; }
            bool isDone() const { return this->tag == InsertResultTag::Done; }
            bool isTree() const { return this->tag == InsertResultTag::Tree; }

            template<typename Fn>
            InsertResult apply(Fn fn) const
            {
                return InsertResult{this->tag, fn(this->tnode)};
            }
        };
        constexpr static InsertResult emptyInsertResult{InsertResultTag::Done, nullptr};

        enum class DeleteResultTag
        {
            Done,
            Short
        };

        class DeleteResult
        {
        public:
            const DeleteResultTag tag;
            const CmpRBNode<K, E>* tnode;

            static DeleteResult makeDone(const CmpRBNode<K, E>* tnode) { return DeleteResult{DeleteResultTag::Done, tnode}; }
            static DeleteResult makeShort(const CmpRBNode<K, E>* tnode) { return DeleteResult{DeleteResultTag::Short, tnode}; }

            bool isDone() const { return this->tag == DeleteResultTag::Done; }
            bool isShort() const { return this->tag == DeleteResultTag::Short; }
        };

        static int64_t checkRBPathLengthInvariant(const CmpRBNode<K, E>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            
            if(isLeafType(node)) {
                return (node->data.color == RColor::Black) ? 1 : 0;
            }
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(node);
            
                int64_t lc = checkRBPathLengthInvariant(tnode->left);
                if(lc == -1) {
                    return -1;
                }

                int64_t rc = checkRBPathLengthInvariant(tnode->right);
                if(rc == -1) {
                    return -1;
                }

                if(lc != rc) { // black height mismatch
                    return -1;
                }

                return (node->data.color == RColor::Black) ? (lc + 1) : lc;
            }
        }

        static bool checkRBChildColorInvariant(const CmpRBNode<K, E>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            } 
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(node);
                
                if(tnode->data.color == RColor::Red) {
                    if(tnode->left != nullptr && tnode->left->data.color == RColor::Red) {
                        return false;
                    }
                    if(tnode->right != nullptr && tnode->right->data.color == RColor::Red) {
                        return false;
                    }
                }

                return checkRBChildColorInvariant(tnode->left) && checkRBChildColorInvariant(tnode->right);
            }

            return true;
        }

        static bool checkRBLeafInvariant(const CmpRBNode<K, E>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            }
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(node);
                
                if(tnode->left == nullptr && tnode->right == nullptr) {
                    return false;
                }

                return checkRBLeafInvariant(tnode->left) && checkRBLeafInvariant(tnode->right);
            }
        }

        static bool checkRBInvariants(const CmpRBNode<K, E>* node)
        {
            return checkRBChildColorInvariant(node) && checkRBPathLengthInvariant(node) >= 0 && checkRBLeafInvariant(node);
        }
            
        static void debugAssertInvariants(const CmpRBNode<K, E>* node, int64_t expectedCount)
        {
            assert(checkRBInvariants(node));
            assert(reprGetCount(node) == expectedCount);
        }

        // double red violation on the LL side  (B (R (R a x b) y c) z d) = T (R (B a x b) y (B c z d))
        static InsertResult balancehelper_RR_LL(const CmpRBNode<K, E>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(cur);

                const CmpRBNode<K, E>* l = reprGetLeft(tnode);
                if(l == nullptr || l->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, E>* ll = reprGetLeft(l);
                if(ll == nullptr || ll->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                return InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(ll), reprGetRight(ll), ll->data), 
                        mkcopynode(RColor::Black, reprGetRight(l), reprGetRight(tnode), tnode->data),
                        l->data
                    )
                );
            }
        }

        // double red violation on the LR side  (B (R a x (R b y c)) z d) = T (R (B a x b) y (B c z d))
        static InsertResult balancehelper_RR_LR(const CmpRBNode<K, E>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(cur);

                const CmpRBNode<K, E>* l  = reprGetLeft(tnode);
                if(l == nullptr || l->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, E>* lr = reprGetRight(l);
                if(lr == nullptr || lr->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                return InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(l), reprGetLeft(lr), l->data), 
                        mkcopynode(RColor::Black, reprGetRight(lr), reprGetRight(tnode), tnode->data),
                        lr->data
                    )
                );
            }
        }

        // double red violation on the RL side  (B a x (R (R b y c) z d)) = T (R (B a x b) y (B c z d))
        static InsertResult balancehelper_RR_RL(const CmpRBNode<K, E>* cur)
        {
            assert(cur != nullptr);
            
            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(cur);

                const CmpRBNode<K, E>* r = reprGetRight(tnode);
                if(r == nullptr || r->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, E>* rl = reprGetLeft(r);
                if(rl == nullptr || rl->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                return InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(tnode), reprGetLeft(rl), tnode->data), 
                        mkcopynode(RColor::Black, reprGetRight(rl), reprGetRight(r), r->data),
                        rl->data
                    )
                );
            }
        }

        // double red violation on the RR side balance (B a x (R b y (R c z d))) = T (R (B a x b) y (B c z d))
        static InsertResult balancehelper_RR_RR(const CmpRBNode<K, E>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, E>* tnode = asNodeType(cur);

                const CmpRBNode<K, E>* r = reprGetRight(tnode);
                if(r == nullptr || r->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, E>* rr = reprGetRight(r);
                if(rr == nullptr || rr->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                return InsertResult::makeTree(
                    mknode(RColor::Red, 
                        mkcopynode(RColor::Black, reprGetLeft(tnode), reprGetLeft(r), tnode->data), 
                        mkcopynode(RColor::Black, reprGetLeft(rr), reprGetRight(rr), rr->data),
                        r->data
                    )
                );
            }
        }

        // Just roll up the black nodes -- balance (B a x b) = D (B a x b)
        static InsertResult balancehelper_S_B(const CmpRBNode<K, E>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            return InsertResult::makeDone(cur);
        }

        // Tentatively roll up the red nodes -- balance (R a x b) = T (R a x b)
        static InsertResult balancehelper_S_R(const CmpRBNode<K, E>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Red) {
                return emptyInsertResult;
            }

            return InsertResult::makeTree(cur);
        }

        static InsertResult balance(const InsertResult& rres)
        {
            if(rres.isDone()) {
                return rres;
            }

            const CmpRBNode<K, E>* cur = rres.tnode;

            InsertResult res_rr_ll = balancehelper_RR_LL(cur);
            if(!res_rr_ll.isEmpty()) {
                return res_rr_ll;
            }

            InsertResult res_rr_lr = balancehelper_RR_LR(cur);
            if(!res_rr_lr.isEmpty()) {
                return res_rr_lr;
            }

            InsertResult res_rr_rl = balancehelper_RR_RL(cur);
            if(!res_rr_rl.isEmpty()) {
                return res_rr_rl;
            }
            
            InsertResult res_rr_rr = balancehelper_RR_RR(cur);
            if(!res_rr_rr.isEmpty()) {
                return res_rr_rr;
            }

            InsertResult res_s_b = balancehelper_S_B(cur);
            if(!res_s_b.isEmpty()) {
                return res_s_b;
            }

            return balancehelper_S_R(cur);
        }

        static InsertResult insertrec(const CmpRBNode<K, E>* curr, const E& entry)
        {
            if(curr == nullptr) {
                //add the element in a new leaf
                CmpRBTreeLeaf<K, E>* nleaf = s_leafallocator->construct(CmpRBData<E>(RColor::Red, 1, entry));
                return InsertResult::makeTree(nleaf);
            }

            if(isLeafType(curr)) {
                const CmpRBTreeLeaf<K, E>* leaf = asLeafType(curr);
                
                if(entry.key == leaf->data.entry.key) {
                    CmpRBNode<K, E>* nnode = copyNodeReplaceData(curr, CmpRBData<E>(leaf->data.color, leaf->data.bheight, entry));
                    return InsertResult::makeDone(nnode);
                }
                else {
                    if(entry.key < leaf->data.entry.key) {
                        CmpRBNode<K, E>* lleaf = s_leafallocator->construct(CmpRBData<E>(RColor::Red, 1, entry));
                        return balance(InsertResult::makeTree(mknode(curr->data.color, lleaf, nullptr, curr->data)));
                    }
                    else {
                        CmpRBTreeLeaf<K, E>* rleaf = s_leafallocator->construct(CmpRBData<E>(RColor::Red, 1, entry));
                        return balance(InsertResult::makeTree(mknode(curr->data.color, nullptr, rleaf, curr->data)));
                    }
                }
            }
            else {
                const CmpRBTreeNode<K, E>* opnode = asNodeType(curr);
                const CmpRBNode<K, E>* l = opnode->left;
                const CmpRBNode<K, E>* r = opnode->right;
                
                if(entry.key < opnode->data.entry.key) {
                    InsertResult nleft = insertrec(l, entry);
                    return balance(nleft.apply([opnode, r](const CmpRBNode<K, E>* tnode) { return mknode(opnode->data.color, tnode, r, opnode->data); }));
                }
                else if(entry.key > opnode->data.entry.key) {
                    InsertResult nright = insertrec(r, entry);
                    return balance(nright.apply([opnode, l](const CmpRBNode<K, E>* tnode) { return mknode(opnode->data.color, l, tnode, opnode->data); }));
                }
                else {
                    CmpRBNode<K, E>* nnode = copyNodeReplaceData(curr, CmpRBData<E>(opnode->data.color, opnode->data.bheight, entry));
                    return InsertResult::makeDone(nnode);
                }
            }
        }

        static CmpRBNode<K, E>* blacken(InsertResult rr)
        {
            if(rr.tnode->data.color == RColor::Black) {
                return const_cast<CmpRBNode<K, E>*>(rr.tnode);
            }
            else {
                return mknode(RColor::Black, reprGetLeft(rr.tnode), reprGetRight(rr.tnode), rr.tnode->data);
            }
        }

    public:
        bool empty() const
        {
            return this->root == nullptr;
        }

        int64_t size() const
        {
            return reprGetCount(this->root);
        }

        template <typename Iter>
        static CmpRBNode<K, E>* mklargerec(Iter start, Iter end)
        {
            CmpRBNode<K, E>* curr = s_leafallocator->construct(CmpRBData<E>(RColor::Red, 1, *start));
            ++start;

            while(start != end) {
                curr = blacken(insertrec(curr, *start));
                ++start;
            }

            return curr;
        }

        E getFrontNode() const
        {
            const CmpRBNode<K, E>* minNode = reprGetMinNode(this->root);
            return minNode->data.entry;
        }

        E getBackNode() const
        {
            const CmpRBNode<K, E>* maxNode = reprGetMaxNode(this->root);
            return maxNode->data.entry;
        }

        E getIndexNode(int64_t index) const
        {
            return reprGetIndexValue(index, this->root);
        }

        bool has(const K& key) const
        {
            return reprGetKeyNode(key, this->root) != nullptr;
        }

        bool tryget(const K& key, E& entry) const
        {
            const CmpRBNode<K, E>* node = reprGetKeyNode(key, this->root);
            if(node != nullptr) {
                entry = node->data.entry;
                return true;
            }

            return false;
        }

        CmpRBTree<K, E, TreeID> insert(const E& entry) const
        {
            CmpRBNode<K, E>* root = blacken(insertrec(this->root, entry));
            BSQ_IF_ENABLED(RB_INVARIANT_VALIDATE, debugAssertInvariants(root, reprGetCount(this->root) + (this->has(entry.key) ? 0 : 1))); //note this->root is never modified so we can test here (after the insert)

            return CmpRBTree<K, E, TreeID>{root};
        }
    };

    template<typename K, typename E, uint32_t TreeID> 
    consteval TypeInfo g_typeinfo_CmpRBTree_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo {
            tid,
            sizeof(CmpRBTree<K, E, TreeID>),
            byteSizeToSlotCount(sizeof(CmpRBTree<K, E, TreeID>)),
            LayoutTag::Ref,
            "1",
            nullptr,
            0,
            nullptr,
            0,
            TypeOpDispatchInfo{},
            tname,
            false
        };
    }
}

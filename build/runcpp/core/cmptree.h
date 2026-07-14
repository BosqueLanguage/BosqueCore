#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "mapentry.h"
#include "integrals.h"

#include "../runtime/allocator/alloc.h"

namespace ᐸRuntimeᐳ
{
    template<typename K, typename V>
    class CmpRBData
    {
    public:
        RColor color;
        uint16_t bheight; //black height of the subtree rooted at this node

        int32_t dcount; //note that when the color follows immediately in enclosing classes the alignment works -- currently this is just use as alignment padding
        XMapEntry<K, V> entry;

        CmpRBData(): color{}, bheight{}, dcount{}, entry{} { ; }
        CmpRBData(const CmpRBData<K, V>& other) = default;

        CmpRBData(RColor color, uint16_t bheight, const CmpRBData<K, V>& data) : color{color}, bheight{bheight}, dcount{1}, entry{data.entry} { ; }
        CmpRBData(RColor color, uint16_t bheight, const XMapEntry<K, V>& value) : color{color}, bheight{bheight}, dcount{1}, entry{value} { ; }
        CmpRBData(RColor color, uint16_t bheight, const K& key, const V& value) : color{color}, bheight{bheight}, dcount{1}, entry{key, value} { ; }

        void toValues(std::vector<XMapEntry<K, V>>& result) const
        {
            result.push_back(this->entry);
        }

        template <typename Fn>
        std::string toJSON(Fn pf) const
        {
            std::string result = "{color: " + std::string((this->color == RColor::Red) ? "Red" : "Black") + ", bheight: " + std::to_string(this->bheight) + ", data: [";
            result += pf(this->entry);
            result += "]}";
            
            return result;
        }

        template<typename Fn>
        void diagnosticEmit(std::ostream& out, Fn diagnosticEmitFn, bool waddr) const
        {
            diagnosticEmitFn(out, this->entry, waddr);
        }
    };

    template<typename K, typename V> class CmpRBTreeLeaf;
    template<typename K, typename V> class CmpRBTreeNode;

    template<typename K, typename V>
    class CmpRBNode
    {
    public:
        const CmpRBData<K, V> data;

        CmpRBNode() : data{} { ; }
        CmpRBNode(const CmpRBNode<K, V>& other) = default;

        CmpRBNode(const CmpRBData<K, V>& data) : data{data} { ; }
        CmpRBNode(RColor color, uint16_t bheight, const CmpRBData<K, V>& data) : data{color, bheight, data} { ; }
    };

    template<typename K, typename V>
    class CmpRBTreeLeaf : public CmpRBNode<K, V>
    {
    public:
        CmpRBTreeLeaf() : CmpRBNode<K, V>{} { ; }
        CmpRBTreeLeaf(const CmpRBTreeLeaf& other) = default;

        CmpRBTreeLeaf(const CmpRBData<K, V>& data) : CmpRBNode<K, V>{data} { ; }
        CmpRBTreeLeaf(RColor color, uint16_t bheight, const CmpRBData<K, V>& data) : CmpRBNode<K, V>{color, bheight, data} { ; }
    };

    template<typename K, typename V>
    consteval TypeInfo g_typeinfo_CmpRBTreeLeaf_generate(uint32_t tid, const char* mask, const char* tname, bool quickrelease)
    {
        return TypeInfo{
            tid,
            sizeof(CmpRBTreeLeaf<K, V>),
            byteSizeToSlotCount(sizeof(CmpRBTreeLeaf<K, V>)),
            LayoutTag::Ref,
            mask,
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            tname,
            quickrelease
        };
    }

    template<typename K, typename V> 
    class CmpRBTreeNode : public CmpRBNode<K, V>
    {
    public:
        const CmpRBNode<K, V>* left;
        const CmpRBNode<K, V>* right;
        int64_t tcount; //total number of elements in the subtree rooted at this node

        CmpRBTreeNode() : CmpRBNode<K, V>{}, left{}, right{}, tcount{} { ; }
        CmpRBTreeNode(const CmpRBTreeNode& other) = default;

        CmpRBTreeNode(RColor color, uint16_t bheight, int64_t tcount, const CmpRBNode<K, V>* left, const CmpRBNode<K, V>* right, const CmpRBData<K, V>& data) : CmpRBNode<K, V>{color, bheight, data}, left{left}, right{right}, tcount{tcount} { ; }
    };

    template<typename K, typename V> 
    consteval TypeInfo g_typeinfo_CmpRBTreeNode_generate(uint32_t tid, const char* mask, const char* tname)
    {
        return TypeInfo{
            tid,
            sizeof(CmpRBTreeNode<K, V>),
            byteSizeToSlotCount(sizeof(CmpRBTreeNode<K, V>)),
            LayoutTag::Ref,
            mask,
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            tname,
            false
        };
    }

    template<typename K, typename V, uint32_t TreeID>
    class CmpRBTree
    {
    public:
        CmpRBNode<K, V>* root;

        static const TypeInfo* s_leaftypeinfo;
        thread_local static GCAllocator<CmpRBTreeLeaf<K, V>>* s_leafallocator;

        static const TypeInfo* s_nodetypeinfo;
        thread_local static GCAllocator<CmpRBTreeNode<K, V>>* s_nodeallocator;

        CmpRBTree() : root{} { ; }
        CmpRBTree(CmpRBNode<K, V>* node) : root{node} { ; }
        CmpRBTree(const CmpRBTree& other) = default;

        static bool isLeafType(const CmpRBNode<K, V>* node) { return (node != nullptr) && (gcGetTypeInfo(const_cast<CmpRBNode<K, V>*>(node)) == s_leaftypeinfo); }
        static bool isNodeType(const CmpRBNode<K, V>* node) { return (node != nullptr) && (gcGetTypeInfo(const_cast<CmpRBNode<K, V>*>(node)) == s_nodetypeinfo); }

        static const CmpRBTreeLeaf<K, V>* asLeafType(const CmpRBNode<K, V>* node) { return static_cast<const CmpRBTreeLeaf<K, V>*>(node); }
        static const CmpRBTreeNode<K, V>* asNodeType(const CmpRBNode<K, V>* node) { return static_cast<const CmpRBTreeNode<K, V>*>(node); }

        static int64_t reprGetBHeight(const CmpRBNode<K, V>* node)
        {
            return (node != nullptr) ? node->data.bheight : 1;
        }

        static int64_t reprGetCount(const CmpRBNode<K, V>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            else {
                return (isLeafType(node)) ? node->data.dcount : asNodeType(node)->tcount;
            }
        }

        static const CmpRBNode<K, V>* reprGetLeft(const CmpRBNode<K, V>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->left : nullptr;
        }

        static const CmpRBNode<K, V>* reprGetRight(const CmpRBNode<K, V>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->right : nullptr;
        }

        static uint16_t computeNewBHeight_ForTreeLeaf(RColor color) { return 1 + ((color == RColor::Black) ? 1 : 0); }
        static uint16_t computeNewBHeight_ForTreeNode(RColor color, const CmpRBNode<K, V>* left, const CmpRBNode<K, V>* right) { return reprGetBHeight(left) + ((color == RColor::Black) ? 1 : 0); }
        static int64_t computeNewCount_ForTreeNode(const CmpRBNode<K, V>* left, const CmpRBNode<K, V>* right, const CmpRBData<K, V>& data) { return reprGetCount(left) + reprGetCount(right) + data.dcount; }

        template <typename Iter>
        static CmpRBNode<K, V>* mkinitial(const XMapEntry<K, V>& value)
        {
            return s_leafallocator->construct(CmpRBData<K, V>(RColor::Black, 2, value));
        }

        static CmpRBNode<K, V>* mknode(RColor color, const CmpRBNode<K, V>* left, const CmpRBNode<K, V>* right, const CmpRBData<K, V>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator->construct(color, computeNewBHeight_ForTreeLeaf(color), data);
            }
            else {
                return s_nodeallocator->construct(color, computeNewBHeight_ForTreeNode(color, left, right), computeNewCount_ForTreeNode(left, right, data), left, right, data);
            }
        }

        static CmpRBNode<K, V>* copyNodeReplaceData(const CmpRBNode<K, V>* node, const CmpRBData<K, V>& ndata)
        {
            if(isLeafType(node)) {
                return s_leafallocator->construct(node->data.color, computeNewBHeight_ForTreeLeaf(node->data.color), ndata);
            }  
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(node);
                return s_nodeallocator->construct(node->data.color, computeNewBHeight_ForTreeNode(node->data.color, tnode->left, tnode->right), computeNewCount_ForTreeNode(tnode->left, tnode->right, ndata), tnode->left, tnode->right, ndata);
            }
        }

        static CmpRBNode<K, V>* mkcopynode(RColor color, const CmpRBNode<K, V>* left, const CmpRBNode<K, V>* right, const CmpRBData<K, V>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator->construct(color, computeNewBHeight_ForTreeLeaf(color), data);
            }
            else {
                return s_nodeallocator->construct(color, computeNewBHeight_ForTreeNode(color, left, right), computeNewCount_ForTreeNode(left, right, data), left, right, data);
            }
        }

        static const CmpRBNode<K, V>* reprGetMinNode(const CmpRBNode<K, V>* curr)
        {
            while(reprGetLeft(curr) != nullptr) {
                curr = reprGetLeft(curr);
            }
            return curr;
        }

        static const CmpRBNode<K, V>* reprGetMaxNode(const CmpRBNode<K, V>* curr)
        {
            while(reprGetRight(curr) != nullptr) {
                curr = reprGetRight(curr);
            }
            return curr;
        }

        static XMapEntry<K, V> reprGetIndexValue(int64_t index, const CmpRBNode<K, V>* curr)
        {
            while(true) {
                if(isLeafType(curr)) {
                    return curr->data.entry;
                }
                else {
                    const CmpRBTreeNode<K, V>* tnode = asNodeType(curr);
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

        static const CmpRBNode<K, V>* reprGetKeyNode(const K& key, const CmpRBNode<K, V>* curr)
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

        static V reprGetKeyValue(const K& key, const CmpRBNode<K, V>* curr)
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
        
        static void reprToValues(std::vector<XMapEntry<K, V>>& result, const CmpRBNode<K, V>* node)
        {
            if(node == nullptr) {
                return;
            }
            else {
                const CmpRBNode<K, V>* ll = reprGetLeft(node);
                const CmpRBNode<K, V>* rr = reprGetRight(node);
                
                if(ll != nullptr) {
                    reprToValues(result, ll);
                }
                
                node->data.entry.toValues(result);

                if(rr != nullptr) {
                    reprToValues(result, rr);
                }

                return;
            }
        }

        template <typename Fn>
        static std::string reprToJSON(const CmpRBNode<K, V>* node, Fn pf)
        {
            if(node == nullptr) {
                return "null";
            }
            else {
                const CmpRBNode<K, V>* ll = reprGetLeft(node);
                const CmpRBNode<K, V>* rr = reprGetRight(node);
                
                return "{node: " + node->data.entry.toJSON(pf) + ", left: " + reprToJSON(ll, pf) + ", right: " + reprToJSON(rr, pf) + "}";
            }
        }

        void toValues(std::vector<XMapEntry<K, V>>& result) const
        {
            reprToValues(result, this->root);
        }

        template <typename Fn>
        std::string toJSON(Fn pf) const
        {
            return reprToJSON(this->root, pf);
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
            const CmpRBNode<K, V>* tnode;

            static InsertResult makeDone(const CmpRBNode<K, V>* tnode) { return InsertResult{InsertResultTag::Done, tnode}; }
            static InsertResult makeTree(const CmpRBNode<K, V>* ptree) { return InsertResult{InsertResultTag::Tree, ptree}; }

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
            const CmpRBNode<K, V>* tnode;

            static DeleteResult makeDone(const CmpRBNode<K, V>* tnode) { return DeleteResult{DeleteResultTag::Done, tnode}; }
            static DeleteResult makeShort(const CmpRBNode<K, V>* tnode) { return DeleteResult{DeleteResultTag::Short, tnode}; }

            bool isDone() const { return this->tag == DeleteResultTag::Done; }
            bool isShort() const { return this->tag == DeleteResultTag::Short; }
        };

        static int64_t checkRBPathLengthInvariant(const CmpRBNode<K, V>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            
            if(isLeafType(node)) {
                return (node->data.color == RColor::Black) ? 1 : 0;
            }
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(node);
            
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

        static bool checkRBChildColorInvariant(const CmpRBNode<K, V>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            } 
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(node);
                
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

        static bool checkRBLeafInvariant(const CmpRBNode<K, V>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            }
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(node);
                
                if(tnode->left == nullptr && tnode->right == nullptr) {
                    return false;
                }

                return checkRBLeafInvariant(tnode->left) && checkRBLeafInvariant(tnode->right);
            }
        }

        static bool checkRBInvariants(const CmpRBNode<K, V>* node)
        {
            return checkRBChildColorInvariant(node) && checkRBPathLengthInvariant(node) >= 0 && checkRBLeafInvariant(node);
        }
            
        static void debugAssertInvariants(const CmpRBNode<K, V>* node, int64_t expectedCount)
        {
            assert(checkRBInvariants(node));
            assert(reprGetCount(node) == expectedCount);
        }

        // double red violation on the LL side  (B (R (R a x b) y c) z d) = T (R (B a x b) y (B c z d))
        static InsertResult balancehelper_RR_LL(const CmpRBNode<K, V>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(cur);

                const CmpRBNode<K, V>* l = reprGetLeft(tnode);
                if(l == nullptr || l->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, V>* ll = reprGetLeft(l);
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
        static InsertResult balancehelper_RR_LR(const CmpRBNode<K, V>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(cur);

                const CmpRBNode<K, V>* l  = reprGetLeft(tnode);
                if(l == nullptr || l->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, V>* lr = reprGetRight(l);
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
        static InsertResult balancehelper_RR_RL(const CmpRBNode<K, V>* cur)
        {
            assert(cur != nullptr);
            
            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(cur);

                const CmpRBNode<K, V>* r = reprGetRight(tnode);
                if(r == nullptr || r->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, V>* rl = reprGetLeft(r);
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
        static InsertResult balancehelper_RR_RR(const CmpRBNode<K, V>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const CmpRBTreeNode<K, V>* tnode = asNodeType(cur);

                const CmpRBNode<K, V>* r = reprGetRight(tnode);
                if(r == nullptr || r->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const CmpRBNode<K, V>* rr = reprGetRight(r);
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
        static InsertResult balancehelper_S_B(const CmpRBNode<K, V>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            return InsertResult::makeDone(cur);
        }

        // Tentatively roll up the red nodes -- balance (R a x b) = T (R a x b)
        static InsertResult balancehelper_S_R(const CmpRBNode<K, V>* cur)
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

            const CmpRBNode<K, V>* cur = rres.tnode;

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

        static InsertResult insertrec(const CmpRBNode<K, V>* curr, const K& key, const V& value)
        {
            if(curr == nullptr) {
                //add the element in a new leaf
                CmpRBTreeLeaf<K, V>* nleaf = s_leafallocator->construct(CmpRBData<K, V>(RColor::Red, 1, key, value));
                return InsertResult::makeTree(nleaf);
            }

            if(isLeafType(curr)) {
                const CmpRBTreeLeaf<K, V>* leaf = asLeafType(curr);
                
                if(key == leaf->data.entry.key) {
                    CmpRBNode<K, V>* nnode = copyNodeReplaceData(curr, CmpRBData<K, V>(leaf->data.color, leaf->data.bheight, key, value));
                    return InsertResult::makeDone(nnode);
                }
                else {
                    if(key < leaf->data.entry.key) {
                        CmpRBNode<K, V>* lleaf = s_leafallocator->construct(CmpRBData<K, V>(RColor::Red, 1, key, value));
                        return balance(InsertResult::makeTree(mknode(curr->data.color, lleaf, nullptr, curr->data)));
                    }
                    else {
                        CmpRBTreeLeaf<K, V>* rleaf = s_leafallocator->construct(CmpRBData<K, V>(RColor::Red, 1, key, value));
                        return balance(InsertResult::makeTree(mknode(curr->data.color, nullptr, rleaf, curr->data)));
                    }
                }
            }
            else {
                const CmpRBTreeNode<K, V>* opnode = asNodeType(curr);
                const CmpRBNode<K, V>* l = opnode->left;
                const CmpRBNode<K, V>* r = opnode->right;
                
                if(key < opnode->data.entry.key) {
                    InsertResult nleft = insertrec(l, key, value);
                    return balance(nleft.apply([opnode, r](const CmpRBNode<K, V>* tnode) { return mknode(opnode->data.color, tnode, r, opnode->data); }));
                }
                else if(key > opnode->data.entry.key) {
                    InsertResult nright = insertrec(r, key, value);
                    return balance(nright.apply([opnode, l](const CmpRBNode<K, V>* tnode) { return mknode(opnode->data.color, l, tnode, opnode->data); }));
                }
                else {
                    CmpRBNode<K, V>* nnode = copyNodeReplaceData(curr, CmpRBData<K, V>(opnode->data.color, opnode->data.bheight, key, value));
                    return InsertResult::makeDone(nnode);
                }
            }
        }

        static CmpRBNode<K, V>* blacken(InsertResult rr)
        {
            if(rr.tnode->data.color == RColor::Black) {
                return const_cast<CmpRBNode<K, V>*>(rr.tnode);
            }
            else {
                return mknode(RColor::Black, reprGetLeft(rr.tnode), reprGetRight(rr.tnode), rr.tnode->data);
            }
        }

        template <typename Fn>
        static void recdiagnosticEmit(const CmpRBNode<K, V>* curr, std::ostream& out, Fn diagnosticEmitFn, bool waddr)
        {
            if(curr == nullptr) {
                out << "()";
                return;
            }

            if(waddr) {
                out << "@" << curr;
            }
            out << "(";

            if(isLeafType(curr)) {
                curr->data.diagnosticEmit(out, diagnosticEmitFn, waddr);
            }
            else {
                recdiagnosticEmit(reprGetLeft(curr), out, diagnosticEmitFn, waddr);
                curr->data.diagnosticEmit(out, diagnosticEmitFn, waddr);
                recdiagnosticEmit(reprGetRight(curr), out, diagnosticEmitFn, waddr);
            }
                
            out << ")";
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
        static CmpRBNode<K, V>* mklargerec(Iter start, Iter end)
        {
            CmpRBNode<K, V>* curr = s_leafallocator->construct(CmpRBData<K, V>(RColor::Red, 1, start->key, start->value));
            ++start;

            while(start != end) {
                curr = blacken(insertrec(curr, start->key, start->value));
                ++start;
            }

            return curr;
        }

        XMapEntry<K, V> getFrontNode() const
        {
            const CmpRBNode<K, V>* minNode = reprGetMinNode(this->root);
            return minNode->data.entry;
        }

        XMapEntry<K, V> getBackNode() const
        {
            const CmpRBNode<K, V>* maxNode = reprGetMaxNode(this->root);
            return maxNode->data.entry;
        }

        XMapEntry<K, V> getIndexNode(int64_t index) const
        {
            return reprGetIndexValue(index, this->root);
        }

        bool has(const K& key) const
        {
            return reprGetKeyNode(key, this->root) != nullptr;
        }

        V getValue(const K& key) const
        {
            return reprGetKeyValue(key, this->root);
        }

        bool tryget(const K& key, V& val) const
        {
            const CmpRBNode<K, V>* node = reprGetKeyNode(key, this->root);
            if(node != nullptr) {
                val = node->data.entry.value;
                return true;
            }

            return false;
        }

        CmpRBTree<K, V, TreeID> insert(const K& key, const V& value) const
        {
            CmpRBNode<K, V>* root = blacken(insertrec(this->root, key, value));

            BSQ_IF_ENABLED(RB_INVARIANT_VALIDATE, debugAssertInvariants(root, reprGetCount(this->root) + 1));
            return CmpRBTree<K, V, TreeID>{root};
        }

        template <typename Fn>
        void diagnosticEmit(std::ostream& out, const TypeInfo* ltype, Fn diagnosticEmitFn, bool waddr) const
        {
            out << ltype->typekey << "{";
            recdiagnosticEmit(this->root, out, diagnosticEmitFn, waddr);
            out << "}";
        }
    };

    template<typename K, typename V, uint32_t TreeID> 
    consteval TypeInfo g_typeinfo_CmpRBTree_generate(uint32_t tid, const char* tname)
    {
        return TypeInfo {
            tid,
            sizeof(CmpRBTree<K, V, TreeID>),
            byteSizeToSlotCount(sizeof(CmpRBTree<K, V, TreeID>)),
            LayoutTag::Ref,
            "1",
            nullptr,
            0,
            nullptr,
            0,
            nullptr,
            0,
            tname,
            false
        };
    }
}

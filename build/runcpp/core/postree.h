#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "integrals.h"
#include "boxed.h"

#include "../runtime/allocator/alloc.h"

#define BSQ_POSTREE_VALIDATE 1

#ifdef BSQ_POSTREE_VALIDATE
#define BSQ_POSTREE_ASSERT(COND) assert(COND)
#else
#define BSQ_POSTREE_ASSERT(COND) ((void)0)
#endif

namespace ᐸRuntimeᐳ
{
    template <int64_t K>
    constexpr std::array<XNat, K> create_idx_range() {
        std::array<XNat, K> arr;
        for(int64_t i = 0; i < K; ++i) {
            arr[i] = XNat{i};
        }
        
        return arr;
    }

    template <int64_t K>
    std::array<XNat, K> create_idx_range_from(int64_t start) {
        std::array<XNat, K> arr;
        for(int64_t i = 0; i < K; ++i) {
            arr[i] = XNat{i + start};
        }
        
        return arr;
    }

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
        std::array<T, K> data;

        constexpr PosRBData(): color{}, bheight{}, dcount{}, data{} { ; }
        constexpr PosRBData(RColor color, uint16_t bheight, const PosRBData<T, K>& data) : color{color}, bheight{bheight}, dcount{data.dcount}, data{data.data} { ; }
        constexpr PosRBData(const PosRBData& other) = default;

        constexpr PosRBData(RColor color, uint16_t bheight, const T& value) : color{color}, bheight{bheight}, dcount{1}, data{value} { ; }
        constexpr PosRBData(RColor color, uint16_t bheight, int32_t dcount, const std::array<T, K>& data) : color{color}, bheight{bheight}, dcount{dcount}, data{data} { ; }

        constexpr static void zerofill(std::array<T, K>& data, size_t ecount)
        {
            std::fill(data.begin() + ecount, data.end(), T{});
        }

        /** Constructor when we have a range of values  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter start, Iter end) : color{color}, bheight{bheight}
        {            
            const size_t size = std::distance(start, end);
            assert(size != 0);
            assert(size <= K);

            std::copy(start, end, this->data.begin());
            this->dcount = size; 
            
            if(size < K) {
                zerofill(this->data, size);
            }
        }

        /** Constructor when we have a single value at position 0 and a range of values that follow -- pushFront style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, const T& ival, Iter rstart, Iter rend) : color{color}, bheight{bheight}
        {   
            const size_t size = 1 + std::distance(rstart, rend);
            assert(size <= K);

            this->data[0] = ival;
            std::copy(rstart, rend, this->data.begin() + 1);
            this->dcount = size;

            if(size < K) {
                zerofill(this->data, size);
            }
        }

        /** Constructor when we have a range of values and a single value at the end -- pushBack style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter lstart, Iter lend, const T& ival) : color{color}, bheight{bheight}
        {          
            const size_t size = std::distance(lstart, lend) + 1;
            assert(size <= K);

            std::copy(lstart, lend, this->data.begin());
            this->data[std::distance(lstart, lend)] = ival;
            this->dcount = size;

            if(size < K) {
                zerofill(this->data, size);
            }
        }

        /** Constructor when we have a range of values, a single value, and then another range of values -- insert middle style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter lstart, Iter lend, const T& ival, Iter rstart, Iter rend) : color{color}, bheight{bheight}
        {
            const size_t size = std::distance(lstart, lend) + 1 + std::distance(rstart, rend);
            assert(size <= K);

            std::copy(lstart, lend, this->data.begin());
            this->data[std::distance(lstart, lend)] = ival;
            std::copy(rstart, rend, this->data.begin() + std::distance(lstart, lend) + 1);
            this->dcount = size;

            if(size < K) {
                zerofill(this->data, size);
            }
        }

        /** Constructor when we have a range of values and then another range of values -- remove middle style constructor  **/
        template<typename Iter>
        PosRBData(RColor color, uint16_t bheight, Iter lstart, Iter lend, Iter rstart, Iter rend) : color{color}, bheight{bheight}
        {
            const size_t size = std::distance(lstart, lend) + std::distance(rstart, rend);
            assert(size <= K);

            std::copy(lstart, lend, this->data.begin());
            std::copy(rstart, rend, this->data.begin() + std::distance(lstart, lend));
            this->dcount = size;

            if(size < K) {
                zerofill(this->data, size);
            }
        }

        PosRBData pushfront(const T& value) const
        {
            assert((size_t)this->dcount < K);
            return PosRBData(this->color, this->bheight, value, this->data.begin(), this->data.begin() + this->dcount);
        }

        PosRBData pushback(const T& value) const
        {
            assert((size_t)this->dcount < K);
            return PosRBData(this->color, this->bheight, this->data.begin(), this->data.begin() + this->dcount, value);
        }

        PosRBData insert(int64_t index, const T& value) const
        {
            assert((0 <= index) & (index <= this->dcount));
            assert((size_t)this->dcount < K);

            if(index == 0) {
                return PosRBData(this->color, this->bheight, value, this->data.begin(), this->data.begin() + this->dcount);
            }
            else if(index == this->dcount) {
                return PosRBData(this->color, this->bheight, this->data.begin(), this->data.begin() + this->dcount, value);
            }
            else {
                return PosRBData(this->color, this->bheight, this->data.begin(), this->data.begin() + index, value, this->data.begin() + index, this->data.begin() + this->dcount);
            }
        }

        PosRBData insertSpillLeft(int64_t index, const T& value, T& spill) const
        {
            assert((0 <= index) & (index < (int64_t)K));
            assert((size_t)this->dcount == K);
          
            if(index == 0) {
                spill = value;
                return *this;
            }
            else {
                spill = this->data[0];
                return PosRBData(this->color, this->bheight, this->data.begin() + 1, this->data.begin() + index, value, this->data.begin() + index, this->data.end());
            }
        }

        PosRBData insertSpillRight(int64_t index, const T& value, T& spill) const
        {
            assert((0 < index) & (index <= (int64_t)K));
            assert((size_t)this->dcount == K);
          
            if(index == K) {
                spill = value;
                return *this;
            }
            else {
                spill = this->data[K - 1];
                return PosRBData(this->color, this->bheight, this->data.begin(), this->data.begin() + index, value, this->data.begin() + index, this->data.begin() + (K - 1));
            }
        }

        PosRBData set(int64_t index, const T& value) const
        {
            assert((0 <= index) & (index < this->dcount));
            return PosRBData(this->color, this->bheight, this->data.begin(), this->data.begin() + index, value, this->data.begin() + index + 1, this->data.begin() + this->dcount);
        }

        PosRBData remove(int64_t index) const
        {
            assert((0 <= index) & (index < this->dcount));
            assert(this->dcount > 1);

            if(index == 0) {
                return PosRBData(this->color, this->bheight, this->data.begin() + 1, this->data.begin() + this->dcount);
            }
            else if(index == this->dcount - 1) {
                return PosRBData(this->color, this->bheight, this->data.begin(), this->data.begin() + this->dcount - 1);
            }
            else {
                return PosRBData(this->color, this->bheight, this->data.begin(), this->data.begin() + index, this->data.begin() + index + 1, this->data.begin() + this->dcount);
            }
        }

#ifdef BSQ_POSTREE_VALIDATE
        void toValues(std::vector<T>& result) const
        {
            for(size_t i = 0; i < (size_t)this->dcount; i++) {
                result.push_back(this->data[i]);
            }
        }

        template <typename Fn>
        std::string toJSON(Fn pf) const
        {
            std::string result = "{color: " + std::string((this->color == RColor::Red) ? "Red" : "Black") + ", bheight: " + std::to_string(this->bheight) + ", data: [";
            for(size_t i = 0; i < (size_t)this->dcount; i++) {
                result += pf(this->data[i]);
                if(i != (size_t)(this->dcount - 1)) {
                    result += ", ";
                }
            }
            result += "]}";
            return result;
        }
#endif

        template<bool SafeSimplePred, typename Pred>
        bool allOf(Pred p) const
        {
            if constexpr (SafeSimplePred) {
                return std::all_of(std::execution::unseq, this->data.begin(), this->data.begin() + this->dcount, p);
            }
            else {
                auto ii = std::find_if_not(this->data.begin(), this->data.begin() + this->dcount, p);
                return ii == (this->data.begin() + this->dcount);
            }
        }

        template<bool SafeSimplePred, typename Pred>
        bool someOf(Pred p) const
        {
            if constexpr (SafeSimplePred) {
                return std::any_of(std::execution::unseq, this->data.begin(), this->data.begin() + this->dcount, p);
            }
            else {
                auto ii = std::find_if(this->data.begin(), this->data.begin() + this->dcount, p);
                return ii != (this->data.begin() + this->dcount);
            }
        }

        template<bool SafeSimplePred, typename Pred>
        bool noneOf(Pred p) const
        {
            if constexpr (SafeSimplePred) {
                return std::none_of(std::execution::unseq, this->data.begin(), this->data.begin() + this->dcount, p);
            }
            else {
                auto ii = std::find_if(this->data.begin(), this->data.begin() + this->dcount, p);
                return ii == (this->data.begin() + this->dcount);
            }
        }

        template<bool SafeSimpleFn, typename U, typename Fn>
        PosRBData<U, K> map(Fn f) const
        {
            std::array<U, K> result{};
            std::transform(this->data.begin(), this->data.begin() + this->dcount, result.begin(), f);
            
            return PosRBData<U, K>(this->color, this->bheight, this->dcount, result);
        }

        template<bool SafeSimpleFn, typename U, typename Fn>
        PosRBData<U, K> mapIdx(int64_t sidx, Fn f) const
        {
            std::array<XNat, K> zipidx = create_idx_range_from<K>(sidx);

            std::array<U, K> result{};
            std::transform(this->data.begin(), this->data.begin() + this->dcount, zipidx.begin(), result.begin(), f);
            
            return PosRBData<U, K>(this->color, this->bheight, this->dcount, result);
        }
    };

    template<typename T, size_t K> class PosRBTreeLeaf;
    template<typename T, size_t K> class PosRBTreeNode;

    template<typename T, size_t K>
    class PosRBNode
    {
    public:
        const PosRBData<T, K> data;

        constexpr PosRBNode() : data{} { ; }
        constexpr PosRBNode(const PosRBNode<T, K>& other) = default;

        constexpr PosRBNode(const PosRBData<T, K>& data) : data{data} { ; }
        constexpr PosRBNode(RColor color, uint16_t bheight, const PosRBData<T, K>& data) : data{color, bheight, data} { ; }
    };

    template<typename T, size_t K>
    class PosRBTreeLeaf : public PosRBNode<T, K>
    {
    public:
        constexpr PosRBTreeLeaf() : PosRBNode<T, K>{} { ; }
        constexpr PosRBTreeLeaf(const PosRBTreeLeaf& other) = default;

        constexpr PosRBTreeLeaf(const PosRBData<T, K>& data) : PosRBNode<T, K>{data} { ; }
        constexpr PosRBTreeLeaf(RColor color, uint16_t bheight, const PosRBData<T, K>& data) : PosRBNode<T, K>{color, bheight, data} { ; }
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
        const PosRBNode<T, K>* left;
        const PosRBNode<T, K>* right;
        int64_t tcount; //total number of elements in the subtree rooted at this node

        constexpr PosRBTreeNode() : PosRBNode<T, K>{}, left{}, right{}, tcount{} { ; }
        constexpr PosRBTreeNode(const PosRBTreeNode& other) = default;

        constexpr PosRBTreeNode(RColor color, uint16_t bheight, int64_t tcount, const PosRBNode<T, K>* left, const PosRBNode<T, K>* right, const PosRBData<T, K>& data) : PosRBNode<T, K>{color, bheight, data}, left{left}, right{right}, tcount{tcount} { ; }
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

    template<typename T, size_t K, uint32_t TreeID>
    class PosRBTree
    {
    public:
        PosRBNode<T, K>* root;

        static const TypeInfo* s_leaftypeinfo;
        thread_local static GCAllocator<PosRBTreeLeaf<T, K>>* s_leafallocator;

        static const TypeInfo* s_nodetypeinfo;
        thread_local static GCAllocator<PosRBTreeNode<T, K>>* s_nodeallocator;

        constexpr PosRBTree() : root{} { ; }
        constexpr PosRBTree(PosRBNode<T, K>* node) : root{node} { ; }
        constexpr PosRBTree(const PosRBTree& other) = default;

        static bool isLeafType(const PosRBNode<T, K>* node) { return (node != nullptr) && (gcGetTypeInfo(const_cast<PosRBNode<T, K>*>(node)) == s_leaftypeinfo); }
        static bool isNodeType(const PosRBNode<T, K>* node) { return (node != nullptr) && (gcGetTypeInfo(const_cast<PosRBNode<T, K>*>(node)) == s_nodetypeinfo); }

        static const PosRBTreeLeaf<T, K>* asLeafType(const PosRBNode<T, K>* node) { return static_cast<const PosRBTreeLeaf<T, K>*>(node); }
        static const PosRBTreeNode<T, K>* asNodeType(const PosRBNode<T, K>* node) { return static_cast<const PosRBTreeNode<T, K>*>(node); }

        static int64_t reprGetBHeight(const PosRBNode<T, K>* node)
        {
            return (node != nullptr) ? node->data.bheight : 1;
        }

        static int64_t reprGetCount(const PosRBNode<T, K>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            else {
                return (isLeafType(node)) ? node->data.dcount : asNodeType(node)->tcount;
            }
        }

        static const PosRBNode<T, K>* reprGetLeft(const PosRBNode<T, K>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->left : nullptr;
        }

        static const PosRBNode<T, K>* reprGetRight(const PosRBNode<T, K>* node) 
        {
            return (isNodeType(node)) ? asNodeType(node)->right : nullptr;
        }

        static uint16_t computeNewBHeight_ForTreeLeaf(RColor color) { return 1 + ((color == RColor::Black) ? 1 : 0); }
        static uint16_t computeNewBHeight_ForTreeNode(RColor color, const PosRBNode<T, K>* left, const PosRBNode<T, K>* right) { return reprGetBHeight(left) + ((color == RColor::Black) ? 1 : 0); }
        static int64_t computeNewCount_ForTreeNode(const PosRBNode<T, K>* left, const PosRBNode<T, K>* right, const PosRBData<T, K>& data) { return reprGetCount(left) + reprGetCount(right) + data.dcount; }

        template <typename Iter>
        static PosRBNode<T, K>* mkinitial(Iter start, Iter end)
        {
            return s_leafallocator->construct(PosRBData<T, K>(RColor::Black, 2, start, end));
        }

        template <typename Iter>
        static PosRBNode<T, K>* mkinitial(const T& value, Iter start, Iter end)
        {
            return s_leafallocator->construct(PosRBData<T, K>(RColor::Black, 2, value, start, end));
        }

        template <typename Iter>
        static PosRBNode<T, K>* mkinitial(Iter start, Iter end, const T& value)
        {
            return s_leafallocator->construct(PosRBData<T, K>(RColor::Black, 2, start, end, value));
        }

        template <typename Iter>
        static PosRBNode<T, K>* mkinitial(Iter lstart, Iter lend, const T& value, Iter rstart, Iter rend)
        {
            return s_leafallocator->construct(PosRBData<T, K>(RColor::Black, 2, lstart, lend, value, rstart, rend));
        }

        static PosRBNode<T, K>* mknode(RColor color, const PosRBNode<T, K>* left, const PosRBNode<T, K>* right, const PosRBData<T, K>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator->construct(color, computeNewBHeight_ForTreeLeaf(color), data);
            }
            else {
                return s_nodeallocator->construct(color, computeNewBHeight_ForTreeNode(color, left, right), computeNewCount_ForTreeNode(left, right, data), left, right, data);
            }
        }

        static PosRBNode<T, K>* copyNodeReplaceData(const PosRBNode<T, K>* node, const PosRBData<T, K>& ndata)
        {
            if(isLeafType(node)) {
                return s_leafallocator->construct(node->data.color, computeNewBHeight_ForTreeLeaf(node->data.color), ndata);
            }  
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(node);
                return s_nodeallocator->construct(node->data.color, computeNewBHeight_ForTreeNode(node->data.color, tnode->left, tnode->right), computeNewCount_ForTreeNode(tnode->left, tnode->right, ndata), tnode->left, tnode->right, ndata);
            }
        }

        static PosRBNode<T, K>* mkcopynode(RColor color, const PosRBNode<T, K>* left, const PosRBNode<T, K>* right, const PosRBData<T, K>& data)
        {
            if(left == nullptr && right == nullptr) {
                return s_leafallocator->construct(color, computeNewBHeight_ForTreeLeaf(color), data);
            }
            else {
                return s_nodeallocator->construct(color, computeNewBHeight_ForTreeNode(color, left, right), computeNewCount_ForTreeNode(left, right, data), left, right, data);
            }
        }

        static const PosRBNode<T, K>* reprGetMinNode(const PosRBNode<T, K>* curr)
        {
            while(reprGetLeft(curr) != nullptr) {
                curr = reprGetLeft(curr);
            }
            return curr;
        }

        static const PosRBNode<T, K>* reprGetMaxNode(const PosRBNode<T, K>* curr)
        {
            while(reprGetRight(curr) != nullptr) {
                curr = reprGetRight(curr);
            }
            return curr;
        }

        static const PosRBNode<T, K>* reprGetIndexNode(int64_t index, const PosRBNode<T, K>* curr)
        {
            while(true) {
                const PosRBNode<T, K>* l = reprGetLeft(curr);
                int64_t lcount = reprGetCount(l);

                if(index < lcount) {
                    curr = l;
                }
                else if(index >= lcount + curr->data.dcount) {
                    index -= (lcount + curr->data.dcount);
                    curr = reprGetRight(curr);
                }
                else {
                    return curr; //index is within the current node
                }
            }
        }
        
#ifdef BSQ_POSTREE_VALIDATE
        static void reprToValues(std::vector<T>& result, const PosRBNode<T, K>* node)
        {
            if(node == nullptr) {
                return;
            }
            else {
                const PosRBNode<T, K>* ll = reprGetLeft(node);
                const PosRBNode<T, K>* rr = reprGetRight(node);
                
                if(ll != nullptr) {
                    reprToValues(result, ll);
                }
                
                node->data.toValues(result);

                if(rr != nullptr) {
                    reprToValues(result, rr);
                }

                return;
            }
        }

        template <typename Fn>
        static std::string reprToJSON(const PosRBNode<T, K>* node, Fn pf)
        {
            if(node == nullptr) {
                return "null";
            }
            else {
                const PosRBNode<T, K>* ll = reprGetLeft(node);
                const PosRBNode<T, K>* rr = reprGetRight(node);
                
                return "{node: " + node->data.toJSON(pf) + ", left: " + reprToJSON(ll, pf) + ", right: " + reprToJSON(rr, pf) + "}";
            }
        }

        void toValues(std::vector<T>& result) const
        {
            reprToValues(result, this->root);
        }

        template <typename Fn>
        std::string toJSON(Fn pf) const
        {
            return reprToJSON(this->root, pf);
        }
#endif

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
            const PosRBNode<T, K>* tnode;

            static InsertResult makeDone(const PosRBNode<T, K>* tnode) { return InsertResult{InsertResultTag::Done, tnode}; }
            static InsertResult makeTree(const PosRBNode<T, K>* ptree) { return InsertResult{InsertResultTag::Tree, ptree}; }

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
            const PosRBNode<T, K>* tnode;

            static DeleteResult makeDone(const PosRBNode<T, K>* tnode) { return DeleteResult{DeleteResultTag::Done, tnode}; }
            static DeleteResult makeShort(const PosRBNode<T, K>* tnode) { return DeleteResult{DeleteResultTag::Short, tnode}; }

            bool isDone() const { return this->tag == DeleteResultTag::Done; }
            bool isShort() const { return this->tag == DeleteResultTag::Short; }
        };

#if BSQ_POSTREE_VALIDATE
        static int64_t checkRBPathLengthInvariant(const PosRBNode<T, K>* node)
        {
            if(node == nullptr) {
                return 0;
            }
            
            if(isLeafType(node)) {
                return (node->data.color == RColor::Black) ? 1 : 0;
            }
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(node);
            
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

        static bool checkRBChildColorInvariant(const PosRBNode<T, K>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            } 
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(node);
                
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

        static bool checkRBLeafInvariant(const PosRBNode<T, K>* node)
        {
            if(node == nullptr || isLeafType(node)) {
                return true;
            }
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(node);
                
                if(tnode->left == nullptr && tnode->right == nullptr) {
                    return false;
                }

                return checkRBLeafInvariant(tnode->left) && checkRBLeafInvariant(tnode->right);
            }
        }

        static bool checkRBInvariants(const PosRBNode<T, K>* node)
        {
            return checkRBChildColorInvariant(node) && checkRBPathLengthInvariant(node) >= 0 && checkRBLeafInvariant(node);
        }
    #endif
            
        static void debugAssertInvariants(const PosRBNode<T, K>* node, int64_t expectedCount)
        {
#if BSQ_POSTREE_VALIDATE
            assert(checkRBInvariants(node));
            assert(reprGetCount(node) == expectedCount);
#endif
        }

        // double red violation on the LL side  (B (R (R a x b) y c) z d) = T (R (B a x b) y (B c z d))
        static InsertResult balancehelper_RR_LL(const PosRBNode<T, K>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBNode<T, K>* l = reprGetLeft(tnode);
                if(l == nullptr || l->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const PosRBNode<T, K>* ll = reprGetLeft(l);
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
        static InsertResult balancehelper_RR_LR(const PosRBNode<T, K>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBNode<T, K>* l  = reprGetLeft(tnode);
                if(l == nullptr || l->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const PosRBNode<T, K>* lr = reprGetRight(l);
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
        static InsertResult balancehelper_RR_RL(const PosRBNode<T, K>* cur)
        {
            assert(cur != nullptr);
            
            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBNode<T, K>* r = reprGetRight(tnode);
                if(r == nullptr || r->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const PosRBNode<T, K>* rl = reprGetLeft(r);
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
        static InsertResult balancehelper_RR_RR(const PosRBNode<T, K>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            if(isLeafType(cur)) {
                return emptyInsertResult;
            }
            else {
                const PosRBTreeNode<T, K>* tnode = asNodeType(cur);

                const PosRBNode<T, K>* r = reprGetRight(tnode);
                if(r == nullptr || r->data.color != RColor::Red) {
                    return emptyInsertResult;
                }

                const PosRBNode<T, K>* rr = reprGetRight(r);
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
        static InsertResult balancehelper_S_B(const PosRBNode<T, K>* cur)
        {
            assert(cur != nullptr);

            if(cur->data.color != RColor::Black) {
                return emptyInsertResult;
            }

            return InsertResult::makeDone(cur);
        }

        // Tentatively roll up the red nodes -- balance (R a x b) = T (R a x b)
        static InsertResult balancehelper_S_R(const PosRBNode<T, K>* cur)
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

            const PosRBNode<T, K>* cur = rres.tnode;

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

        static InsertResult pushfrontrec(const PosRBNode<T, K>* curr, const T& value)
        {
            //add the element in a new leaf
            if(curr == nullptr) {
                PosRBTreeLeaf<T, K>* nleaf = s_leafallocator->construct(PosRBData<T, K>(RColor::Red, 1, value));
                return InsertResult::makeTree(nleaf);
            }

            //we can add the element without modifying structure -- no rebalancing needed just copy spine
            if((size_t)curr->data.dcount < K && reprGetLeft(curr) == nullptr) {
                PosRBNode<T, K>* nnode = copyNodeReplaceData(curr, curr->data.pushfront(value));
                return InsertResult::makeDone(nnode);
            }
            else {
                InsertResult nleft = pushfrontrec(reprGetLeft(curr), value);
                return balance(nleft.apply([curr](const PosRBNode<T, K>* tnode) { return mknode(curr->data.color, tnode, reprGetRight(curr), curr->data); }));
            }
        }

        static InsertResult pushbackrec(const PosRBNode<T, K>* curr, const T& value)
        {
            //add the element in a new leaf
            if(curr == nullptr) {
                PosRBTreeLeaf<T, K>* nleaf = s_leafallocator->construct(PosRBData<T, K>(RColor::Red, 1, value));
                return InsertResult::makeTree(nleaf);
            }

            //we can add the element without modifying structure -- no rebalancing needed just copy spine
            if((size_t)curr->data.dcount < K && reprGetRight(curr) == nullptr) {
                PosRBNode<T, K>* nnode = copyNodeReplaceData(curr, curr->data.pushback(value));
                return InsertResult::makeDone(nnode);
            }
            else {
                InsertResult nright = pushbackrec(reprGetRight(curr), value);
                return balance(nright.apply([curr](const PosRBNode<T, K>* tnode) { return mknode(curr->data.color, reprGetLeft(curr), tnode, curr->data); }));
            }
        }

        static InsertResult insertrec(const PosRBNode<T, K>* curr, int64_t index, const T& value)
        {
            if(curr == nullptr) {
                //add the element in a new leaf
                PosRBTreeLeaf<T, K>* nleaf = s_leafallocator->construct(PosRBData<T, K>(RColor::Red, 1, value));
                return InsertResult::makeTree(nleaf);
            }

            if(isLeafType(curr)) {
                const PosRBTreeLeaf<T, K>* leaf = asLeafType(curr);
                
                if((size_t)curr->data.dcount < K) {
                    PosRBNode<T, K>* nnode = copyNodeReplaceData(curr, curr->data.insert(index, value));
                    return InsertResult::makeDone(nnode);
                }
                else {
                    if(index < (int64_t)K / 2) {
                        //then spill the insert element down to the left
                        T spill;
                        PosRBData<T, K> ndata = curr->data.insertSpillLeft(index, value, spill);
                        PosRBTreeLeaf<T, K>* lleaf = s_leafallocator->construct(PosRBData<T, K>(RColor::Red, 1, spill));
                        return balance(InsertResult::makeTree(mknode(ndata.color, lleaf, nullptr, ndata)));
                    }
                    else {
                        //then spill the insert element down to the right
                        T spill;
                        PosRBData<T, K> ndata = curr->data.insertSpillRight(index, value, spill);
                        PosRBTreeLeaf<T, K>* rleaf = s_leafallocator->construct(PosRBData<T, K>(RColor::Red, 1, spill));
                        return balance(InsertResult::makeTree(mknode(ndata.color, nullptr, rleaf, ndata)));
                    }
                }
            }
            else {
                const PosRBTreeNode<T, K>* opnode = asNodeType(curr);
                const PosRBNode<T, K>* l = opnode->left;
                const PosRBNode<T, K>* r = opnode->right;
                
                int64_t lcount = reprGetCount(l);
                if(index < lcount) {
                    //insert to left
                    if(index == lcount && (size_t)curr->data.dcount < K) {
                        //we can add the element without modifying structure -- no rebalancing needed just copy spine
                        PosRBNode<T, K>* nnode = copyNodeReplaceData(curr, curr->data.pushfront(value));
                        return InsertResult::makeDone(nnode);
                    }
                    else {
                        InsertResult nleft = insertrec(l, index, value);
                        return balance(nleft.apply([opnode, r](const PosRBNode<T, K>* tnode) { return mknode(opnode->data.color, tnode, r, opnode->data); }));
                    }
                }
                else if(index >= lcount + opnode->data.dcount) {
                    //insert to right
                    if(index == lcount + opnode->data.dcount && (size_t)opnode->data.dcount < K) {
                        //we can add the element without modifying structure -- no rebalancing needed just copy spine
                        PosRBNode<T, K>* nnode = copyNodeReplaceData(curr, curr->data.pushback(value));
                        return InsertResult::makeDone(nnode);
                    }
                    else {
                        InsertResult nright = insertrec(r, index - (lcount + opnode->data.dcount), value);
                        return balance(nright.apply([opnode, l](const PosRBNode<T, K>* tnode) { return mknode(opnode->data.color, l, tnode, opnode->data); }));
                    }
                }
                else {
                    int64_t nidx = index - lcount;

                    if((size_t)curr->data.dcount < K) {
                        //we can add the element without modifying structure -- no rebalancing needed just copy spine
                        PosRBNode<T, K>* nnode = copyNodeReplaceData(curr, curr->data.insert(nidx, value));
                        return InsertResult::makeDone(nnode);
                    }
                    else {
                        bool leftspill = (l == nullptr) || (r != nullptr && nidx < (int64_t)K / 2);

                        if(leftspill) {
                            //then spill the insert element down to the left
                            T spill;
                            PosRBData<T, K> ndata = curr->data.insertSpillLeft(nidx, value, spill);
                            InsertResult nleft = pushbackrec(l, spill);
                            return balance(nleft.apply([opnode, r, &ndata](const PosRBNode<T, K>* tnode) { return mknode(ndata.color, tnode, r, ndata); }));
                        }
                        else {
                            //then spill the insert element down to the right
                            T spill;
                            PosRBData<T, K> ndata = curr->data.insertSpillRight(nidx, value, spill);
                            InsertResult nright = pushfrontrec(r, spill);
                            return balance(nright.apply([opnode, l, &ndata](const PosRBNode<T, K>* tnode) { return mknode(ndata.color, l, tnode, ndata); }));
                        }
                    }
                }
            }
        }

        static PosRBNode<T, K>* blacken(InsertResult rr)
        {
            if(rr.tnode->data.color == RColor::Black) {
                return const_cast<PosRBNode<T, K>*>(rr.tnode);
            }
            else {
                return mknode(RColor::Black, reprGetLeft(rr.tnode), reprGetRight(rr.tnode), rr.tnode->data);
            }
        }

        static PosRBNode<T, K>* setrec(const PosRBNode<T, K>* curr, int64_t index, const T& value)
        {
            std::vector<std::pair<const PosRBNode<T, K>*, std::pair<bool, bool>>> path;
            while(true) {
                const PosRBNode<T, K>* l = reprGetLeft(curr);
                int64_t lcount = reprGetCount(l);

                if(index < lcount) {
                    path.push_back(std::make_pair(curr, std::make_pair(true, false)));
                    curr = l;
                }
                else if(index >= lcount + curr->data.dcount) {
                    path.push_back(std::make_pair(curr, std::make_pair(false, true)));
                    index -= (lcount + curr->data.dcount);
                    curr = reprGetRight(curr);
                }
                else {
                    break; //index is within the current node
                }
            }

            //set the value at the specified index within the current node
            PosRBNode<T, K>* nnode = copyNodeReplaceData(curr, curr->data.set(index, value));

            //go back up the path and update each node in the path with the new value
            while(!path.empty()) {
                std::pair<const PosRBNode<T, K>*, std::pair<bool, bool>> pp = path.back();
                path.pop_back();

                if(pp.second.first) {
                    // Update the left child
                    nnode = mkcopynode(pp.first->data.color, nnode, reprGetRight(pp.first), pp.first->data);
                }
                else {
                    // Update the right child
                    nnode = mkcopynode(pp.first->data.color, reprGetLeft(pp.first), nnode, pp.first->data);
                }
            }

            return nnode;
        }

        template<bool SafeSimplePred, typename Pred>
        static bool recallOf(const PosRBNode<T, K>* curr, Pred p)
        {
            if(curr == nullptr) {
                return true;
            }

            if(isLeafType(curr)) {
                return curr->data.template allOf<SafeSimplePred, Pred>(p);
            }
            else {
                bool allleft = recallOf<SafeSimplePred, Pred>(reprGetLeft(curr), p);
                if(!allleft) {
                    return false;
                }

                bool allmid = curr->data.template allOf<SafeSimplePred, Pred>(p);
                if(!allmid) {
                    return false;
                }

                bool allright = recallOf<SafeSimplePred, Pred>(reprGetRight(curr), p);
                if(!allright) {
                    return false;
                }

                return true;
            }
        }

        template<bool SafeSimplePred, typename Pred>
        static bool recnoneOf(const PosRBNode<T, K>* curr, Pred p)
        {
            if(curr == nullptr) {
                return true;
            }

            if(isLeafType(curr)) {
                return curr->data.template noneOf<SafeSimplePred, Pred>(p);
            }
            else {
                bool noneleft = recnoneOf<SafeSimplePred, Pred>(reprGetLeft(curr), p);
                if(!noneleft) {
                    return false;
                }

                bool nonemid = curr->data.template noneOf<SafeSimplePred, Pred>(p);
                if(!nonemid) {
                    return false;
                }

                bool noneright = recnoneOf<SafeSimplePred, Pred>(reprGetRight(curr), p);
                if(!noneright) {
                    return false;
                }

                return true;
            }
        }

        template<bool SafeSimplePred, typename Pred>
        static bool recsomeOf(const PosRBNode<T, K>* curr, Pred p)
        {
            if(curr == nullptr) {
                return false;
            }

            if(isLeafType(curr)) {
                return curr->data.template someOf<SafeSimplePred, Pred>(p);
            }
            else {
                bool someleft = recsomeOf<SafeSimplePred, Pred>(reprGetLeft(curr), p);
                if(someleft) {
                    return true;
                }

                bool somemid = curr->data.template someOf<SafeSimplePred, Pred>(p);
                if(somemid) {
                    return true;
                }

                bool someright = recsomeOf<SafeSimplePred, Pred>(reprGetRight(curr), p);
                if(someright) {
                    return true;
                }

                return false;
            }
        }

        template<bool SafeSimpleFn, typename U, uint32_t UTreeID, typename Fn>
        static PosRBNode<U, K>* recmap(const PosRBNode<T, K>* curr, Fn f)
        {
            if(curr == nullptr) {
                return nullptr;
            }

            if(isLeafType(curr)) {
                return PosRBTree<U, K, UTreeID>::mkcopynode(curr->data.color, nullptr, nullptr, curr->data.template map<SafeSimpleFn, U, Fn>(f));
            }
            else {
                const PosRBNode<U, K>* nleft = recmap<SafeSimpleFn, U, UTreeID, Fn>(reprGetLeft(curr), f);
                const PosRBData<U, K> ndata = curr->data.template map<SafeSimpleFn, U, Fn>(f);
                const PosRBNode<U, K>* nright = recmap<SafeSimpleFn, U, UTreeID, Fn>(reprGetRight(curr), f);

                return PosRBTree<U, K, UTreeID>::mkcopynode(curr->data.color, nleft, nright, ndata);
            }
        }

        template<bool SafeSimpleFn, typename U, uint32_t UTreeID, typename Fn>
        static PosRBNode<U, K>* recmapIdx(const PosRBNode<T, K>* curr, int64_t sidx, Fn f)
        {
            if(curr == nullptr) {
                return nullptr;
            }

            if(isLeafType(curr)) {
                return PosRBTree<U, K, UTreeID>::mkcopynode(curr->data.color, nullptr, nullptr, curr->data.template mapIdx<SafeSimpleFn, U, Fn>(sidx, f));
            }
            else {
                const int64_t leftCount = reprGetCount(reprGetLeft(curr));
                const int64_t midCount = curr->data.dcount;

                const PosRBNode<U, K>* nleft = recmapIdx<SafeSimpleFn, U, UTreeID, Fn>(reprGetLeft(curr), sidx, f);
                const PosRBData<U, K> ndata = curr->data.template mapIdx<SafeSimpleFn, U, Fn>(sidx + leftCount, f);
                const PosRBNode<U, K>* nright = recmapIdx<SafeSimpleFn, U, UTreeID, Fn>(reprGetRight(curr), sidx + leftCount + midCount, f);
                
                return PosRBTree<U, K, UTreeID>::mkcopynode(curr->data.color, nleft, nright, ndata);
            }
        }

    public:
        int64_t size() const
        {
            return reprGetCount(this->root);
        }

        T getFront() const
        {
            const PosRBNode<T, K>* minNode = reprGetMinNode(this->root);
            return minNode->data.data[0];
        }

        T getBack() const
        {
            const PosRBNode<T, K>* maxNode = reprGetMaxNode(this->root);
            return maxNode->data.data[maxNode->data.dcount - 1];
        }

        T get(int64_t index) const
        {
            const PosRBNode<T, K>* indexNode = reprGetIndexNode(index, this->root);
            return indexNode->data.data[index - reprGetCount(reprGetLeft(indexNode))];
        }

        PosRBTree<T, K, TreeID> pushFront(const T& value) const
        {
            PosRBNode<T, K>* root = blacken(pushfrontrec(this->root, value));

            debugAssertInvariants(root, reprGetCount(this->root) + 1);
            return PosRBTree<T, K, TreeID>{root};
        }

        PosRBTree<T, K, TreeID> pushBack(const T& value) const
        {
            PosRBNode<T, K>* root = blacken(pushbackrec(this->root, value));

            debugAssertInvariants(root, reprGetCount(this->root) + 1);
            return PosRBTree<T, K, TreeID>{root};
        }

        PosRBTree<T, K, TreeID> insert(int64_t index, const T& value) const
        {
            PosRBNode<T, K>* root = blacken(insertrec(this->root, index, value));

            debugAssertInvariants(root, reprGetCount(this->root) + 1);
            return PosRBTree<T, K, TreeID>{root};
        }

        PosRBTree<T, K, TreeID> set(int64_t index, const T& value) const
        {
            PosRBNode<T, K>* root = setrec(this->root, index, value);

            debugAssertInvariants(root, reprGetCount(this->root));
            return PosRBTree<T, K, TreeID>{root};
        }

        template<bool SafeSimplePred, typename Pred>
        XBool allof(const Pred& p) const
        {
            return XBool::from(recallOf<SafeSimplePred, Pred>(this->root, p));
        }

        template<bool SafeSimplePred, typename Pred>
        XBool noneof(const Pred& p) const
        {
            return XBool::from(recnoneOf<SafeSimplePred, Pred>(this->root, p));
        }

        template<bool SafeSimplePred, typename Pred>
        XBool someof(const Pred& p) const
        {
            return XBool::from(recsomeOf<SafeSimplePred, Pred>(this->root, p));
        }

        template<bool SafeSimpleFn, typename U, uint32_t UTreeID, typename Fn>
        PosRBTree<U, K, UTreeID> map(Fn f) const
        {
            return PosRBTree<U, K, UTreeID>{recmap<SafeSimpleFn, U, UTreeID, Fn>(this->root, f)};
        }

        template<bool SafeSimpleFn, typename U, uint32_t UTreeID, typename Fn>
        PosRBTree<U, K, UTreeID> mapIdx(Fn f) const
        {
            return PosRBTree<U, K, UTreeID>{recmapIdx<SafeSimpleFn, U, UTreeID, Fn>(this->root, 0, f)};
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

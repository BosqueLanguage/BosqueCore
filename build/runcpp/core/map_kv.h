#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "mapentry.h"
#include "cmptree.h"

namespace ᐸRuntimeᐳ
{
    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    template<typename K, typename V, uint32_t TYPE_ID_CMP_TREE_KV>
    class XMapKVIterator
    {
    public:
        int64_t index;
        CmpRBTree<K, V, TYPE_ID_CMP_TREE_KV> umap;

        using value_type = XMapEntry<K, V>;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(!this->umap.empty());
            
            return this->umap.getindex(this->index);
        }

        XMapKVIterator& operator++()
        {
            this->index++;
            return *this;
        }
 
        XMapKVIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        XMapKVIterator& operator--()
        {
            this->index--;
            return *this;
        }
 
        XMapKVIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const XMapKVIterator& lhs, const XMapKVIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XMapKVIterator& lhs, const XMapKVIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };

    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    class XMapKV
    {
    public:
        consteval static uint32_t getCmpTreeIDFrom(uint32_t treeid) { return treeid - 1; }

        CmpRBTree<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)> utree;

        XMapKV() : utree{} {}
        XMapKV(const XMapKV& other) = default;
        XMapKV(const CmpRBTree<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)>& n) : utree{n} { ; }

        static XMapKV mk(std::initializer_list<XMapEntry<K, V>> elems)
        {
            if(elems.size() == 0) {
                return XMapKV{};
            }
            else {
                return XMapKV(CmpRBTree<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)>::mklargerec(elems.begin(), elems.end()));
            }
        }

        static XMapKV mk(const XMapEntry<K, V>* elems, size_t len)
        {
            if(len == 0) {
                return XMapKV{};
            }
            else {
                return XMapKV(CmpRBTree<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)>::mklargerec(elems, elems + len));
            }
        }

        template <typename Fn>
        std::string toString(Fn pf) const
        {
            if(this->utree.empty()) {
                return "[]";
            }
            else {
                std::vector<XMapEntry<K, V>> values;
                this->utree.toValues(values);

                std::string result = "[";
                for(size_t i = 0; i < values.size(); i++) {
                    result += pf(values[i]);
                    if(i != values.size() - 1) {
                        result += ", ";
                    }
                }
                result += "]";
                return result;
            }
        }

        template <typename Fn>
        std::string toJSON(Fn pf) const
        {
            if(this->utree.empty()) {
                return "null";
            }
            else {
                return this->utree.toJSON(pf);
            }
        }

        bool empty() const
        {
            return this->utree.empty();
        }

        size_t size() const
        {
            return this->utree.size();
        }

        XMapKVIterator<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)> begin() const
        {
            return XMapKVIterator<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)>{0, this->utree};
        }

        XMapKVIterator<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)> end() const
        {
            return XMapKVIterator<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)>{(int64_t)this->size(), this->utree};
        }

        XMapEntry<K, V> getMin() const
        {
            return this->utree.getFront();
        }

        XMapEntry<K, V> getMax() const
        {
            return this->utree.getBack();
        }

        bool has(const K& key) const
        {
            return this->utree.has(key);
        }

        XMapEntry<K, V> get(const K& key) const
        {
            return this->utree.get(key);
        }

        bool tryget(const K& key, XMapEntry<K, V>& val) const
        {
            return this->utree.tryget(key, val);
        }

        XMapKV insert(const K& key, const V& value) const
        {
            CmpRBTree<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)> newtree = this->utree.insert(key, value);
            return XMapKV<K, V, getCmpTreeIDFrom(TYPE_ID_MAP_KV)>{newtree};
        }
    };
}

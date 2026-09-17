#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "mapentry.h"
#include "cmptree.h"

namespace ᐸRuntimeᐳ
{
    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    class XMapKVIterator
    {
    public:
        int64_t index;
        CmpRBTree<K, V, TYPE_ID_MAP_KV> umap;

        using value_type = XMapEntry<K, V>;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(!this->umap.empty());
            
            return this->umap.getIndexNode(this->index);
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
        CmpRBTree<K, V, TYPE_ID_MAP_KV> utree;

        XMapKV() : utree{} {}
        XMapKV(const XMapKV& other) = default;
        XMapKV(const CmpRBTree<K, V, TYPE_ID_MAP_KV>& n) : utree{n} { ; }

        static XMapKV mk(std::initializer_list<XMapEntry<K, V>> elems)
        {
            if(elems.size() == 0) {
                return XMapKV{};
            }
            else {
                return XMapKV(CmpRBTree<K, V, TYPE_ID_MAP_KV>::mklargerec(elems.begin(), elems.end()));
            }
        }

        static XMapKV mk(const XMapEntry<K, V>* elems, size_t len)
        {
            if(len == 0) {
                return XMapKV{};
            }
            else {
                return XMapKV(CmpRBTree<K, V, TYPE_ID_MAP_KV>::mklargerec(elems, elems + len));
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

        XMapKVIterator<K, V, TYPE_ID_MAP_KV> begin() const
        {
            return XMapKVIterator<K, V, TYPE_ID_MAP_KV>{0, this->utree};
        }

        XMapKVIterator<K, V, TYPE_ID_MAP_KV> end() const
        {
            return XMapKVIterator<K, V, TYPE_ID_MAP_KV>{(int64_t)this->size(), this->utree};
        }

        XMapEntry<K, V> getMin() const
        {
            return this->utree.getFrontNode();
        }

        XMapEntry<K, V> getMax() const
        {
            return this->utree.getBackNode();
        }

        bool has(const K& key) const
        {
            return this->utree.has(key);
        }

        V get(const K& key) const
        {
            return this->utree.getValue(key);
        }

        bool tryget(const K& key, V& val) const
        {
            return this->utree.tryget(key, val);
        }

        XMapKV insert(const K& key, const V& value) const
        {
            return XMapKV{this->utree.insert(key, value)};
        }

        XMapKV insert(const XMapEntry<K, V>& entry) const
        {
            return XMapKV{this->utree.insert(entry.key, entry.value)};
        }
    };

    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    void jsonParseToBSQ_MapKV(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array(), "JSON -> BSQ", 0, nullptr, "Expected JSON array List<T>");

        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        XMapKV<K, V, TYPE_ID_MAP_KV> rres{};
        for(size_t i = 0; i < j.size(); i++) {
            XMapEntry<K, V> val;
            kinfo->opdispatch.jsonParseToBSQFp(kinfo, j[i][0], &val.key);
            vinfo->opdispatch.jsonParseToBSQFp(vinfo, j[i][1], &val.value);

            rres = rres.insert(val);
        }

        *(XMapKV<K, V, TYPE_ID_MAP_KV>*)resptr = rres;
    }

    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    void parseToBSQ_MapKV(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected type for MapEntry");
        lexer->consume();
        bsq_validate(lexer->testIsSymbol('{'), "BAPI -> BSQ", 0, nullptr, "Expected '{' for MapEntry");
        lexer->consume();

        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        XMapKV<K, V, TYPE_ID_MAP_KV> rres{};

        bool first = true;
        while(!lexer->testIsSymbol('}')) {
            if(first) {
                first = false;
            }
            else {
                bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' between elements for MapEntry");
                lexer->consume();
            }
            
            XMapEntry<K, V> val;
            kinfo->opdispatch.parseToBSQFp(kinfo, lexer, &val.key);

            bsq_validate(lexer->testIsSymbol("=>"), "BAPI -> BSQ", 0, nullptr, "Expected '=>' between key and value for MapEntry");
            lexer->consume();

            vinfo->opdispatch.parseToBSQFp(vinfo, lexer, &val.value);
            rres = rres.insert(val);
        }

        bsq_validate(lexer->testIsSymbol('}'), "BAPI -> BSQ", 0, nullptr, "Expected '}' for MapEntry");
        lexer->consume();

        *(XMapKV<K, V, TYPE_ID_MAP_KV>*)resptr = rres;
    }

    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    json bsqToJSON_MapKV(const TypeInfo* tinfo, const void* valptr)
    {
        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        json j = json::array();
        const XMapKV<K, V, TYPE_ID_MAP_KV>* map = (const XMapKV<K, V, TYPE_ID_MAP_KV>*)valptr;
        for(auto iter = map->begin(); iter != map->end(); ++iter) {
            XMapEntry<K, V> val = *iter;

            json jk = kinfo->opdispatch.bsqToJSONFp(kinfo, &val.key);
            json jv = vinfo->opdispatch.bsqToJSONFp(vinfo, &val.value);
            
            j.push_back(json::array({jk, jv}));
        }

        return j;

    }

    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    void bsqToBAPI_MapKV(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        const XMapKV<K, V, TYPE_ID_MAP_KV>* map = (const XMapKV<K, V, TYPE_ID_MAP_KV>*)valptr;
        
        if(map->empty())
        {
            builder->appendConstString(tinfo->typekey);
            builder->appendLiteralString("{ }");
            return;
        }
        else {
            builder->appendConstString(tinfo->typekey);
            builder->appendLiteralString("{ ");

            bool first = true;
            for(auto iter = map->begin(); iter != map->end(); ++iter) {
                if(first) {
                    first = false;
                }
                else {
                    builder->appendLiteralString(", ");
                }

                XMapEntry<K, V> val = *iter;
                kinfo->opdispatch.bsqToBAPIFp(kinfo, &val.key, builder);
                builder->appendLiteralString(" => ");
                vinfo->opdispatch.bsqToBAPIFp(vinfo, &val.value, builder);
            }

            builder->appendLiteralString(" }");
        }
    }
    
    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    void displayValue_MapKV(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const TypeInfo* kinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[1].fieldbsqtypeid);

        const XMapKV<K, V, TYPE_ID_MAP_KV>* map = (const XMapKV<K, V, TYPE_ID_MAP_KV>*)valptr;

        if(map->empty()) {
            os << getDisplayIndent(indent) << tinfo->typekey << "{ }";
            return;
        }
        else {
            os << getDisplayIndent(indent) << tinfo->typekey << "{ ";
            bool first = true;
            for(auto iter = map->begin(); iter != map->end(); ++iter) {
                if(first) {
                    first = false;
                }
                else {
                    os << ", ";
                }

                XMapEntry<K, V> val = *iter;
                kinfo->opdispatch.displayFp(kinfo, &val.key, os, indent);
                os << " => ";
                vinfo->opdispatch.displayFp(vinfo, &val.value, os, indent);
            }
            os << " }";
        }
    }

    template<typename K, typename V, uint32_t TYPE_ID_MAP_KV>
    consteval TypeInfo g_typeinfo_MapKV_generate(uint32_t id, const TypeLayoutInfo* layout, const char* mask, const char* name) 
    {
        return TypeInfo{
            id,
            8,
            1,
            LayoutTag::Value,
            mask,
            nullptr,
            0,
            layout,
            1,
            nullptr,
            0,
            TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_MapKV<K, V, TYPE_ID_MAP_KV>, (ParseToBSQFp)&parseToBSQ_MapKV<K, V, TYPE_ID_MAP_KV>, (BSQToJSONFp)&bsqToJSON_MapKV<K, V, TYPE_ID_MAP_KV>, (BSQToBAPIFp)&bsqToBAPI_MapKV<K, V, TYPE_ID_MAP_KV>, (DisplayValueFp)&displayValue_MapKV<K, V, TYPE_ID_MAP_KV> },
            name,
            false
        };
    }
}

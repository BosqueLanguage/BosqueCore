#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "mapentry.h"
#include "cmptree.h"

namespace ᐸRuntimeᐳ
{
 
    template<typename T>
    class XSetEntry
    {
    public:
        T key;

        XSetEntry() = default;
        XSetEntry(const T &v) : key{v} {}
    };

    //TODO: this is currently n * ln(n) for iteration and access -- definitely want to speed this up later
    template<typename T, uint32_t TYPE_ID_SET_T>
    class XSetTIterator
    {
    public:
        int64_t index;
        CmpRBTree<T, XSetEntry<T>, TYPE_ID_SET_T> uset;

        using value_type = T;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        value_type operator*() const 
        { 
            assert(!this->uset.empty());
            
            return this->uset.getIndexNode(this->index).key;
        }

        XSetTIterator& operator++()
        {
            this->index++;
            return *this;
        }
 
        XSetTIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        XSetTIterator& operator--()
        {
            this->index--;
            return *this;
        }
 
        XSetTIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const XSetTIterator& lhs, const XSetTIterator& rhs)
        {
            return lhs.index == rhs.index;
        }

        friend bool operator!=(const XSetTIterator& lhs, const XSetTIterator& rhs) 
        {
            return lhs.index != rhs.index;
        }
    };

    template<typename T, uint32_t TYPE_ID_SET_T>
    class XSetT
    {
    public:
        CmpRBTree<T, XSetEntry<T>, TYPE_ID_SET_T> uset;

        XSetT() : uset{} {}
        XSetT(const XSetT& other) = default;
        XSetT(const CmpRBTree<T, XSetEntry<T>, TYPE_ID_SET_T>& n) : uset{n} { ; }

        static XSetT mk(std::initializer_list<T> elems)
        {
            if(elems.size() == 0) {
                return XSetT{};
            }
            else {
                return XSetT(CmpRBTree<T, XSetEntry<T>, TYPE_ID_SET_T>::mklargerec(elems.begin(), elems.end()));
            }
        }

        static XSetT mk(const T* elems, size_t len)
        {
            if(len == 0) {
                return XSetT{};
            }
            else {
                return XSetT(CmpRBTree<T, XSetEntry<T>, TYPE_ID_SET_T>::mklargerec(elems, elems + len));
            }
        }

        bool empty() const
        {
            return this->uset.empty();
        }

        size_t size() const
        {
            return this->uset.size();
        }

        XSetTIterator<T, TYPE_ID_SET_T> begin() const
        {
            return XSetTIterator<T, TYPE_ID_SET_T>{0, this->uset};
        }

        XSetTIterator<T, TYPE_ID_SET_T> end() const
        {
            return XSetTIterator<T, TYPE_ID_SET_T>{(int64_t)this->size(), this->uset};
        }

        T getMin() const
        {
            return this->uset.getFrontNode().key;
        }

        T getMax() const
        {
            return this->uset.getBackNode().key;
        }

        bool has(const T& v) const
        {
            return this->uset.has(v);
        }

        XSetT insert(const T& v) const
        {
            return XSetT{this->uset.insert(XSetEntry<T>{v})};
        }
    };

    template<typename T, uint32_t TYPE_ID_SET_T>
    void jsonParseToBSQ_SetT(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array(), "JSON -> BSQ", 0, nullptr, "Expected JSON array Set<T>");

        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        XSetT<T, TYPE_ID_SET_T> rres{};
        for(size_t i = 0; i < j.size(); i++) {
            T val;
            vinfo->opdispatch.jsonParseToBSQFp(vinfo, j[i], &val);

            rres = rres.insert(val);
        }

        *(XSetT<T, TYPE_ID_SET_T>*)resptr = rres;
    }

    template<typename T, uint32_t TYPE_ID_SET_T>
    void parseToBSQ_SetT(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected type for Set<T>");
        lexer->consume();
        bsq_validate(lexer->testIsSymbol('{'), "BAPI -> BSQ", 0, nullptr, "Expected '{' for Set<T>");
        lexer->consume();

        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        XSetT<T, TYPE_ID_SET_T> rres{};

        bool first = true;
        while(!lexer->testIsSymbol('}')) {
            if(first) {
                first = false;
            }
            else {
                bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' between elements for Set<T>");
                lexer->consume();
            }
            
            T val;
            vinfo->opdispatch.parseToBSQFp(vinfo, lexer, &val);
            rres = rres.insert(val);
        }

        bsq_validate(lexer->testIsSymbol('}'), "BAPI -> BSQ", 0, nullptr, "Expected '}' for Set<T>");
        lexer->consume();

        *(XSetT<T, TYPE_ID_SET_T>*)resptr = rres;
    }

    template<typename T, uint32_t TYPE_ID_SET_T>
    json bsqToJSON_SetT(const TypeInfo* tinfo, const void* valptr)
    {
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        json j = json::array();
        const XSetT<T, TYPE_ID_SET_T>* set = (const XSetT<T, TYPE_ID_SET_T>*)valptr;
        for(auto iter = set->begin(); iter != set->end(); ++iter) {
            T val = *iter;
            json jv = vinfo->opdispatch.bsqToJSONFp(vinfo, &val);
            
            j.push_back(jv);
        }

        return j;

    }

    template<typename T, uint32_t TYPE_ID_SET_T>
    void bsqToBAPI_SetT(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        const XSetT<T, TYPE_ID_SET_T>* set = (const XSetT<T, TYPE_ID_SET_T>*)valptr;
        
        if(set->empty())
        {
            builder->appendConstString(tinfo->typekey);
            builder->appendLiteralString("{ }");
            return;
        }
        else {
            builder->appendConstString(tinfo->typekey);
            builder->appendLiteralString("{ ");

            bool first = true;
            for(auto iter = set->begin(); iter != set->end(); ++iter) {
                if(first) {
                    first = false;
                }
                else {
                    builder->appendLiteralString(", ");
                }

                T val = *iter;
                vinfo->opdispatch.bsqToBAPIFp(vinfo, &val, builder);
            }

            builder->appendLiteralString(" }");
        }
    }
    
    template<typename T, uint32_t TYPE_ID_SET_T>
    void displayValue_SetT(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const TypeInfo* vinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        const XSetT<T, TYPE_ID_SET_T>* set = (const XSetT<T, TYPE_ID_SET_T>*)valptr;

        if(set->empty()) {
            os << getDisplayIndent(indent) << tinfo->typekey << "{ }";
            return;
        }
        else {
            os << getDisplayIndent(indent) << tinfo->typekey << "{ ";
            bool first = true;
            for(auto iter = set->begin(); iter != set->end(); ++iter) {
                if(first) {
                    first = false;
                }
                else {
                    os << ", ";
                }

                T val = *iter;
                vinfo->opdispatch.displayFp(vinfo, &val, os, indent);
            }
            os << " }";
        }
    }

    template<typename T, uint32_t TYPE_ID_SET_T>
    consteval TypeInfo g_typeinfo_SetT_generate(uint32_t id, const TypeLayoutInfo* layout, const char* mask, const char* name) 
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
            2,
            TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_SetT<T, TYPE_ID_SET_T>, (ParseToBSQFp)&parseToBSQ_SetT<T, TYPE_ID_SET_T>, (BSQToJSONFp)&bsqToJSON_SetT<T, TYPE_ID_SET_T>, (BSQToBAPIFp)&bsqToBAPI_SetT<T, TYPE_ID_SET_T>, (DisplayValueFp)&displayValue_SetT<T, TYPE_ID_SET_T> },
            name,
            false
        };
    }
}

#include "bsqon_parse.h"

#include <inttypes.h>

namespace BSQON
{
    std::vector<std::string> s_coreTypes = {
        "None", "Bool", "Int", "Nat", "BigInt", "BigNat", "Rational", "Float", "Decimal", "String", "ASCIIString",
        "ByteBuffer", "DateTime", "UTCDateTime", "PlainDate", "PlainTime", "TickTime", "LogicalTime", "ISOTimeStamp", "UUIDv4", "UUIDv7", "SHAContentHash", 
        "Regex", "Nothing"
    };

    std::vector<TypeTag> s_okTypeTaggedTags = {
        TypeTag::TYPE_STD_ENTITY,
        TypeTag::TYPE_RECORD, TypeTag::TYPE_TUPLE,
        TypeTag::TYPE_SOMETHING, TypeTag::TYPE_OK, TypeTag::TYPE_ERROR,
        TypeTag::TYPE_LIST, TypeTag::TYPE_STACK, TypeTag::TYPE_QUEUE, TypeTag::TYPE_SET, TypeTag::TYPE_MAP_ENTRY, TypeTag::TYPE_MAP
    };

    bool s_isLeapYear(uint16_t y)
    {
        if(y == 1900 || y == 2100 || y == 2200) {
            return false;
        }
        else {
            return y % 4 == 0;
        }
    }

    bool s_dayInMonth(uint8_t d, uint8_t m, uint16_t y)
    {
        if(m == 1) {
            if(s_isLeapYear(y)) {
                return d <= 29;
            }
            else {
                return d <= 28;
            }
        }
        else {
            if(m == 3 || m == 5 || m == 8 || m == 10) {
                return d <= 30;
            }
            else {
                return d <= 31;
            }
        }
    }

    bool Parser::isValidNat(const std::string nv, int64_t& vv)
    {
        auto ecount = sscanf(nv.c_str(), "%" SCNu64, &vv);
        return ecount == 1 && 0 <= vv && vv <= Type::MAX_SAFE_NUMBER; 
    }

    bool Parser::isValidInt(const std::string nv, int64_t& vv)
    {
        auto ecount = sscanf(nv.c_str(), "%" SCNd64, &vv);
        return ecount == 1 && Type::MIN_SAFE_NUMBER <= vv && vv <= Type::MAX_SAFE_NUMBER;
    }

    bool Parser::isValidFloat(const std::string nv, double& vv)
    {
        auto ecount = sscanf(nv.c_str(), "%lf", &vv);
        return ecount == 1;
    }

    bool Parser::isValidWCTime(const std::string nv, uint64_t& vv)
    {
        auto ecount = sscanf(nv.c_str(), "%" SCNu64, &vv);
        return ecount == 1;
    }

    bool Parser::processDateInfo(const std::string& ds, uint16_t& yy, uint8_t& mm, uint8_t& dd)
    {
        auto pp = sscanf(ds.c_str(), "%4" SCNu16 "-%2" SCNu8 "-%2" SCNu8, &yy, &mm, &dd);

        return pp == 3 && (1900 <= yy && yy <= 2200) && mm < 12 && s_dayInMonth(dd, mm, yy);
    }

    bool Parser::processTimeInfo(const std::string& ds, uint8_t& hh, uint8_t& mm, uint8_t& ss)
    {
        auto pp = sscanf(ds.c_str(), "%2" SCNu8 ":%2" SCNu8 ":%2" SCNu8, &hh, &mm, &ss);

        return pp == 3 && hh < 24 && mm < 60 && ss < 61;
    }

    bool Parser::processMillisInfo(const std::string& ds, uint16_t& millis)
    {
        auto pp = sscanf(ds.c_str(), ".%3" SCNu16, &millis);

        return pp == 1 && millis < 1000;
    }

    bool Parser::processTZInfo(const std::string& ds, const char** tz)
    {
        std::string ttz;
        if(ds.starts_with("{")) {
            ttz = ds.substr(1, ds.size() - 2); //trim {...}
        }
        else {
            ttz = ds;
        }

        auto tzii = this->tzset.insert(ttz);
        *tz = tzii.first->c_str();
        
        return true;
    }

    std::optional<std::vector<Value*>> Parser::processEntriesForTuple(const TupleType* ttype, BSQON_AST_BracketValueNode* node)
    {
        std::vector<Value*> elems;

        auto titer = ttype->entries.cbegin();
        for(auto curr = node->values; curr != NULL; curr = curr->next) {
            elems.push_back(this->parseValue(this->assembly->resolveType(*titer++), curr->value));
        }

        if(elems.size() != ttype->entries.size()) {
            this->addError("Tuple value has incorrect number of elements", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else {
            return std::make_optional(std::move(elems));
        }
    }

    std::optional<std::vector<std::pair<std::string, Value*>>> Parser::processPropertiesForRecord(const RecordType* ttype, BSQON_AST_BraceValueNode* node)
    {
        std::vector<std::pair<std::string, Value*>> props;

        for(auto curr = node->entries; curr != NULL; curr = curr->next) {
            if(curr->value->name == NULL) {
                this->addError("Record value has unnamed property", Parser::convertSrcPos(node->base.pos));
            }
            else {
                std::string pname(curr->value->name);

                auto ptypeiter = std::find_if(ttype->entries.cbegin(), ttype->entries.cend(), [&pname](const RecordTypeEntry& rr) { return rr.pname == pname; });
                if(ptypeiter == ttype->entries.cend()) {
                    this->addError("Unknown property name " + pname, Parser::convertSrcPos(node->base.pos));
                }
                else {
                    if(std::find_if(props.cbegin(), props.cend(), [&pname](const std::pair<std::string, Value*>& pp) { return pp.first == pname; }) != props.cend()) {
                        this->addError("Duplicate property name " + pname, Parser::convertSrcPos(node->base.pos));
                    }
                    else {
                        props.push_back(std::make_pair(pname, this->parseValue(this->assembly->resolveType(ptypeiter->ptype), curr->value->value)));
                    }
                }
            }
        }

        if(props.size() != ttype->entries.size()) {
            this->addError("Record value has mismatched properties", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else {
            std::sort(props.begin(), props.end(), [](const std::pair<std::string, Value*>& a, const std::pair<std::string, Value*>& b) { return a.first < b.first; });
            return std::make_optional(std::move(props));
        }
    }

    std::optional<std::vector<Value*>> Parser::processPropertiesForEntity(const StdEntityType* ttype, BSQON_AST_BraceValueNode* node)
    {
        std::vector<Value*> vals(ttype->fields.size(), nullptr);

        //pass over values to set named fields
        for(auto curr = node->entries; curr != NULL; curr = curr->next) {
            if(curr->value->name != NULL) {
                std::string pname(curr->value->name);

                auto fiter = std::find_if(ttype->fields.cbegin(), ttype->fields.cend(), [&pname](const EntityTypeFieldEntry& pp) { return pp.fname == pname; });
                if(fiter == ttype->fields.cend()) {
                    this->addError("Unknown field name " + pname, Parser::convertSrcPos(node->base.pos));
                }
                else {
                    auto idx = std::distance(ttype->fields.cbegin(), fiter);
                    if(vals[idx] != nullptr) {
                        this->addError("Duplicate field entry " + pname, Parser::convertSrcPos(node->base.pos));
                    }
                    else {
                        vals[idx] = this->parseValue(this->assembly->resolveType(fiter->ftype), curr->value->value);
                    }
                }
            }
        }

        //pass over values to fill in positional fields
        auto positer = std::find_if(vals.begin(), vals.end(), [](Value* vv) { return vv == nullptr; });
        for(auto curr = node->entries; curr != NULL; curr = curr->next) {
            if(curr->value->name == NULL) {
                if(positer == vals.cend()) {
                    this->addError("Too many values for type", Parser::convertSrcPos(node->base.pos));
                }
                else {
                    auto fpos = std::distance(vals.begin(), positer);
                    const EntityTypeFieldEntry& fentry = ttype->fields[fpos];

                    Value* vv = this->parseValue(this->assembly->resolveType(fentry.ftype), curr->value->value);
                    *positer = vv;

                    positer = std::find_if(positer++, vals.end(), [](Value* vv) { return vv == nullptr; });
                }
            }
        }

        if(positer != vals.cend()) {
            this->addError("Too few values for type", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else {
            return std::make_optional(std::move(vals));
        }
    }

    std::optional<Value*> Parser::processPropertiesForSpecialCons(const Type* etype, BSQON_AST_BraceValueNode* node)
    {
        if(node->entries == NULL) {
            this->addError("Missing argument", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else if(node->entries->next != NULL) {
            this->addError("Too many arguments", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else if(node->entries->value->name != NULL) {
            this->addError("Special constructors for value does not accept named fields", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else {
            return std::make_optional(this->parseValue(etype, node->entries->value->value));
        }
    }

    std::optional<std::pair<Value*, Value*>> Parser::processPropertiesForMapEntry(const Type* ktype, const Type* vtype, BSQON_AST_BraceValueNode* node)
    {
        if(node->entries == NULL || node->entries->next == NULL) {
            this->addError("Missing argument", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else if(node->entries->next->next != NULL) {
            this->addError("Too many arguments", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else if(node->entries->value->name != NULL || node->entries->next->value->name != NULL) {
            this->addError("MapEntry value does not accept named fields", Parser::convertSrcPos(node->base.pos));
            return std::nullopt;
        }
        else {
            return std::make_optional(std::make_pair(this->parseValue(ktype, node->entries->value->value), this->parseValue(vtype, node->entries->next->value->value)));
        }
    }

    void Parser::processEntriesForSequence(const Type* etype, BSQON_AST_Node* node, std::vector<Value*>& vals)
    {
        if(node->tag == BSQON_AST_TAG_BracketValue) {
            auto bnode = BSQON_AST_asBracketValueNode(node);
            for(auto curr = bnode->values; curr != NULL; curr = curr->next) {
                vals.push_back(this->parseValue(etype, curr->value));
            }
        }
        else {
            auto bnode = BSQON_AST_asBraceValueNode(node);
            for(auto curr = bnode->entries; curr != NULL; curr = curr->next) {
                if(curr->value->name != NULL) {
                    this->addError("Sequence value cannot have named property", Parser::convertSrcPos(node->pos));
                }
                vals.push_back(this->parseValue(etype, curr->value->value));
            }
        }
    }
        
    void Parser::processEntriesForMap(const Type* keytype, const Type* valtype, BSQON_AST_BraceValueNode* node, std::vector<MapEntryValue*>& entries)
    {
        const Type* metype = this->assembly->resolveType("MapEntry<" + keytype->tkey + ", " + valtype->tkey + ">");

        for(auto curr = node->entries; curr != NULL; curr = curr->next) {
            if(curr->value->name != NULL) {
                this->addError("Map value has named property", Parser::convertSrcPos(node->base.pos));
            }
            else {
                entries.push_back(static_cast<MapEntryValue*>(this->parseValue(metype, curr->value->value)));
            }
        }
    }

    const Type* Parser::resolveTypeFromNameList(std::string basenominal, std::vector<const Type*> terms)
    {
        std::string baseprefix = basenominal.substr(0, basenominal.find("::"));

        std::string scopedname;
        if (this->assembly->namespaces.at("Core")->hasTypenameDecl(basenominal)) {
            scopedname = basenominal;
        }
        else if (this->importmap.find(baseprefix) != this->importmap.end()) {
            scopedname = this->importmap.at(baseprefix) + basenominal.substr(baseprefix.size());
        }
        else {
            if (this->assembly->namespaces.find(baseprefix) != this->assembly->namespaces.end()) {
                scopedname = basenominal;
            }
            else {
                scopedname = this->defaultns + "::" + basenominal;
            }
        }

        if (!terms.empty()) {
            scopedname = scopedname + "<" + std::accumulate(terms.cbegin(), terms.cend(), std::string(), [](std::string&& a, const Type* b) { return a + ", " + b->tkey; }) + ">";
        }

        auto titer = this->assembly->typerefs.find(scopedname);
        if (titer != this->assembly->typerefs.end()) {
            return titer->second;
        }
        else {
            auto aiter = this->assembly->aliasmap.find(scopedname);
            if(aiter != this->assembly->aliasmap.end()) {
                return aiter->second;
            }
            else {
                return UnresolvedType::singleton;
            }
        }
    }

    const Type* Parser::resolveAndCheckType(TypeKey tkey, SourcePos spos)
    {
        auto tt = this->assembly->resolveType(tkey);
        if(tt->isUnresolved()) {
            this->addError("Could not resolve type " + tkey, spos);
        }
            
        return tt;
    }

    const Type* Parser::processCoreType(std::string tname) 
    {
        return this->resolveTypeFromNameList(tname, {});
    }

    bool Parser::parseTemplateTermList(BSQON_TYPE_AST_List* tlist, std::vector<const Type*>& terms) 
    {
        for(auto curr = tlist; curr != NULL; curr = curr->next) {
            terms.push_back(this->parseType(curr->value));
        }
     
        return std::find_if(terms.begin(), terms.end(), [](const Type* tt) { return tt->isUnresolved(); }) == terms.end();
    }

    const Type* Parser::parseTemplateTermList_One(SourcePos spos, BSQON_TYPE_AST_List* tlist) 
    {
        std::vector<const Type*> terms;
        bool ok = this->parseTemplateTermList(tlist, terms);

        if(ok && terms.size() == 1) {
            return terms[0];
        }
        else {
            if(terms.size() != 1) {
                this->addError("Expected 1 template arg but got " + std::to_string(terms.size()), spos);
            }
            return UnresolvedType::singleton;
        }
    }

    std::pair<const Type*, const Type*> Parser::parseTemplateTermList_Two(SourcePos spos, BSQON_TYPE_AST_List* tlist) 
    {
        std::vector<const Type*> terms;
        bool ok = this->parseTemplateTermList(tlist, terms);

        if(ok && terms.size() == 2) {
            return std::make_pair(terms[0], terms[1]);
        }
        else {
            if(terms.size() != 2) {
                this->addError("Expected 2 template arg but got " + std::to_string(terms.size()), spos);
            }
            return std::make_pair(UnresolvedType::singleton, UnresolvedType::singleton);
        }
    }

    const Type* Parser::parseTemplateTypeHelper_One(std::string sname, SourcePos spos, BSQON_TYPE_AST_List* tlist)
    {
        const Type* oftype = this->parseTemplateTermList_One(spos, tlist);
            
        if(oftype->isUnresolved()) {
            return UnresolvedType::singleton;
        } 
        else {
            return this->resolveAndCheckType(sname + "<" + oftype->tkey + ">", spos);
        }
    }

    const Type* Parser::parseTemplateTypeHelper_Two(std::string sname, SourcePos spos, BSQON_TYPE_AST_List* tlist)
    {
        std::pair<const Type*, const Type*> oftype = this->parseTemplateTermList_Two(spos, tlist);
            
        if(oftype.first->isUnresolved() || oftype.second->isUnresolved()) {
            return UnresolvedType::singleton;
        } 
        else {
            return this->resolveAndCheckType(sname + "<" + oftype.first->tkey + ", " + oftype.second->tkey + ">", spos);
        }
    }

    const Type* Parser::parseTemplateTypeHelper_OkErr(const Type* tresult, std::string sname, SourcePos spos)
    {
        if(tresult->isUnresolved()) {
            return UnresolvedType::singleton;
        } 
        else {
            return this->resolveAndCheckType(tresult->tkey + "::" + sname , spos);
        }
    }

    const Type* Parser::parseNominalType(BSQON_TYPE_AST_NominalNode* node)
    {
        std::string tname(node->name);

        bool iscore = std::find(s_coreTypes.begin(), s_coreTypes.end(), tname) != s_coreTypes.end();
        if (iscore) {
            return this->processCoreType(tname);
        }
        else if (tname == "StringOf") {
            return this->parseStringOfType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "ASCIIStringOf") {
            return this->parseASCIIStringOfType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Something") {
            return this->parseSomethingType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Option") {
            return this->parseOptionType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Result") {
            return this->parseResultType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Path") {
            return this->parsePathType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "PathFragment") {
            return this->parsePathFragmentType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "PathGlob") {
            return this->parsePathGlobType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "List") {
            return this->parseListType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Stack") {
            return this->parseStackType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Queue") {
            return this->parseQueueType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Set") {
            return this->parseSetType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "MapEntry") {
            return this->parseMapEntryType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Set") {
            return this->parseMapType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else {
            std::vector<const Type*> terms;
            this->parseTemplateTermList(node->terms, terms);
                
            if(std::any_of(terms.begin(), terms.end(), [](const Type* tt) { return tt->isUnresolved(); })) {
                return UnresolvedType::singleton;
            }
            else {
                return this->resolveTypeFromNameList(tname, terms);
            }
        }
    }

    const Type* Parser::parseNominalTemplateType(BSQON_TYPE_AST_NominalExtNode* node)
    {
        const Type* roottype = this->parseNominalType(node->root);
        if(!roottype->tkey.starts_with("Result<")) {
            this->addError("Expected Result type", Parser::convertSrcPos(node->root->base.pos));
            return UnresolvedType::singleton;
        }
        
        std::string etype = std::string(node->ext);
        if(etype == "Ok") {
            return this->parseTemplateTypeHelper_OkErr(roottype, "Ok", Parser::convertSrcPos(node->base.pos));
        }
        else if(etype == "Err") {
            return this->parseTemplateTypeHelper_OkErr(roottype, "Err", Parser::convertSrcPos(node->base.pos));
        }
        else {
            this->addError("Expected Result::Ok or Result::Err type", Parser::convertSrcPos(node->root->base.pos));
            return UnresolvedType::singleton;
        }
    }

    const Type* Parser::parseTupleType(BSQON_TYPE_AST_TupleNode* node)
    {
        std::vector<const Type*> types;
        this->parseTemplateTermList(node->types, types);
                
        if(std::any_of(types.cbegin(), types.cend(), [](const Type* tt) { return tt->isUnresolved(); })) {
            return UnresolvedType::singleton;
        }
        else {
            std::vector<TypeKey> kk;
            std::transform(types.cbegin(), types.cend(), std::back_inserter(kk), [](const Type* tt){ return tt->tkey; });

            auto tkey = "[" + std::accumulate(kk.begin(), kk.end(), std::string(), [](std::string&& a, TypeKey& b) { return (a == "" ? "" : std::move(a) + ", ") + b; }) + "]";
            return this->resolveAndCheckType(tkey, Parser::convertSrcPos(node->base.pos));
        }
    }

    const Type* Parser::parseRecordType(BSQON_TYPE_AST_RecordNode* node) 
    {
        std::vector<RecordTypeEntry> entries;
        for(auto curr = node->entries; curr != NULL; curr = curr->next) {
            auto pname = std::string(curr->value->name);
            auto ptype = this->parseType(curr->value->value);
            
            if(ptype->isUnresolved()) {
                return UnresolvedType::singleton;
            }
            else {
                entries.push_back(RecordTypeEntry{pname, ptype->tkey});
            }
        }

        std::sort(entries.begin(), entries.end(), [](const RecordTypeEntry& a, const RecordTypeEntry& b) { return a.pname < b.pname; });
        auto tkey = "{" + std::accumulate(entries.cbegin(), entries.cend(), std::string(), [](std::string&& a, const RecordTypeEntry& b) { return (a == "" ? "" : std::move(a) + ", ") + b.pname + ": " + b.ptype; }) + "}";
        return this->resolveAndCheckType(tkey, Parser::convertSrcPos(node->base.pos));
    }

    void Parser::parseConceptSetType_Helper(BSQON_TYPE_AST_Node* node, std::vector<const Type*>& tlist)
    {
        if(node->tag != BSQON_TYPE_AST_TAG_Conjunction) {
            tlist.push_back(this->parseType(node));
        }
        else {
            BSQON_TYPE_AST_Conjunction* cnode = BSQON_AST_asConjunction(node);
            this->parseConceptSetType_Helper(cnode->left, tlist);
            this->parseConceptSetType_Helper(cnode->right, tlist);
        }
    }

    const Type* Parser::parseConceptSetType(BSQON_TYPE_AST_Conjunction* node) 
    {
        std::vector<const Type*> conjs;
        this->parseConceptSetType_Helper(node->left, conjs);
        this->parseConceptSetType_Helper(node->right, conjs);
                
        if(std::any_of(conjs.cbegin(), conjs.cend(), [](const Type* tt) { return tt->isUnresolved(); })) {
            return UnresolvedType::singleton;
        }

        //
        //TODO: Assume that there is no subsumption here -- later we will want to check for this 
        //  Add a subtype relation in the Assembly and check/sort here.

        std::vector<TypeKey> concepts;
        std::transform(conjs.cbegin(), conjs.cend(), std::back_inserter(concepts), [](const Type* tt){ return tt->tkey; });

        std::sort(concepts.begin(), concepts.end());
        auto tkey = std::accumulate(concepts.cbegin(), concepts.cend(), std::string(), [](std::string&& a, const TypeKey& b) { return (a == "" ? "" : std::move(a) + "&") + b; });
        return this->resolveAndCheckType(tkey, Parser::convertSrcPos(node->base.pos));
    }

    void Parser::parseUnionType_Helper(BSQON_TYPE_AST_Node* node, std::vector<const Type*>& tlist)
    {
        if(node->tag != BSQON_TYPE_AST_TAG_Union) {
            tlist.push_back(this->parseType(node));
        }
        else {
            BSQON_TYPE_AST_Union* unode = BSQON_AST_asUnion(node);
            this->parseUnionType_Helper(unode->left, tlist);
            this->parseUnionType_Helper(unode->right, tlist);
        }
    }

    const Type* Parser::parseUnionType(BSQON_TYPE_AST_Union* node)
    {
        std::vector<const Type*> opts;
        this->parseUnionType_Helper(node->left, opts);
        this->parseUnionType_Helper(node->right, opts);
                
        if(std::any_of(opts.cbegin(), opts.cend(), [](const Type* tt) { return tt->isUnresolved(); })) {
            return UnresolvedType::singleton;
        }

        //
        //TODO: Assume that there is no subsumption here -- later we will want to check for this 
        //  Add a subtype relation in the Assembly and check/sort here.
        
        std::vector<TypeKey> disjuncts;
        std::transform(opts.cbegin(), opts.cend(), std::back_inserter(disjuncts), [](const Type* tt){ return tt->tkey; });

        std::sort(disjuncts.begin(), disjuncts.end());
        auto tkey = std::accumulate(disjuncts.cbegin(), disjuncts.cend(), std::string(), [](std::string&& a, const TypeKey& b) { return (a == "" ? "" : std::move(a) + " | ") + b; });
        return this->resolveAndCheckType(tkey, Parser::convertSrcPos(node->base.pos));
    }

    const Type* Parser::parseType(BSQON_TYPE_AST_Node* node)
    {
        switch(node->tag)
        {
            case BSQON_TYPE_AST_TAG_Error:
                return UnresolvedType::singleton;
            case BSQON_TYPE_AST_TAG_Nominal:
                return this->parseNominalType(BSQON_AST_asNominalNode(node));
            case BSQON_TYPE_AST_TAG_NominalExt:
                return this->parseNominalTemplateType(BSQON_AST_asNominalExtNode(node));
            case BSQON_TYPE_AST_TAG_Tuple:
                return this->parseTupleType(BSQON_AST_asTupleNode(node));
            case BSQON_TYPE_AST_TAG_Record:
                return this->parseRecordType(BSQON_AST_asRecordNode(node));
            case BSQON_TYPE_AST_TAG_Conjunction:
                return this->parseConceptSetType(BSQON_AST_asConjunction(node));
            case BSQON_TYPE_AST_TAG_Union:
                return this->parseUnionType(BSQON_AST_asUnion(node));
            default: {
                assert(false);
                return UnresolvedType::singleton;
            }
        }
    }

    const Type* Parser::parseTypeRoot(BSQON_TYPE_AST_Node* node)
    {
        auto ftype = this->parseType(node);

        if(this->assembly->typerefs.find(ftype->tkey) == this->assembly->typerefs.end()) {
            this->addError("Could not resolve type " + ftype->tkey, Parser::convertSrcPos(node->pos));
            return UnresolvedType::singleton;
        }

        return ftype;
    }

    Value* Parser::parseNone(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_None) {
            this->addError("Expected none", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new NoneValue(t, Parser::convertSrcPos(node->pos));
    }
    
    Value* Parser::parseNothing(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Nothing) {
            this->addError("Expected nothing", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new NothingValue(t, Parser::convertSrcPos(node->pos));
    }

    Value* Parser::parseBool(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_True && node->tag != BSQON_AST_TAG_False) {
            this->addError("Expected Boolean literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new BoolValue(t, Parser::convertSrcPos(node->pos), node->tag == BSQON_AST_TAG_True);
    }

    Value* Parser::parseNat(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Nat) {
            this->addError("Expected Nat literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        int64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'n'

        if(!Parser::isValidNat(nv, vv)) {
            this->addError("Nat value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new NatNumberValue(t, Parser::convertSrcPos(node->pos), (uint64_t)vv);
    }

    Value* Parser::parseInt(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Int) {
            this->addError("Expected Int literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        int64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'i'

        if(!Parser::isValidInt(nv, vv)) {
            this->addError("Int value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new IntNumberValue(t, Parser::convertSrcPos(node->pos), vv);
    }

    Value* Parser::parseBigNat(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BigNat) {
            this->addError("Expected BigNat literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'N'

        if(nv.front() == '+') {
            nv = nv.substr(1);
        }

        boost::multiprecision::mpz_int pv(nv);

        return new BigNatNumberValue(t, Parser::convertSrcPos(node->pos), pv);
    }

    Value* Parser::parseBigInt(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BigInt) {
            this->addError("Expected BigInt literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'I'

        if(nv.front() == '+') {
            nv = nv.substr(1);
        }

        boost::multiprecision::mpz_int pv(nv);

        return new BigIntNumberValue(t, Parser::convertSrcPos(node->pos), pv);
    }

    Value* Parser::parseRational(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Rational) {
            this->addError("Expected Rational literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'R'

        if(nv.front() == '+') {
            nv = nv.substr(1);
        }

        if(nv.find('/') == std::string::npos) {
            boost::multiprecision::mpz_int rv(nv);

            return new RationalNumberValue(t, Parser::convertSrcPos(node->pos), boost::multiprecision::mpq_rational(rv, 1));
        }
        else {
            boost::multiprecision::mpz_int numerator(nv.substr(0, nv.find('/')));
            auto denominator = nv.substr(nv.find('/') + 1);

            int64_t denomv;
            if(!Parser::isValidNat(denominator, denomv)) {
                this->addError("Rational numerator outside of valid range", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            return new RationalNumberValue(t, Parser::convertSrcPos(node->pos), boost::multiprecision::mpq_rational(numerator, (uint64_t)denomv));
        }
    }

    Value* Parser::parseFloat(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Float) {
            this->addError("Expected Float literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        double vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'f'

        if(!Parser::isValidFloat(nv, vv)) {
            this->addError("Invalid Float literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new FloatNumberValue(t, Parser::convertSrcPos(node->pos), vv);
    }

    Value* Parser::parseDecimal(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Decimal) {
            this->addError("Expected Decimal literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'd'

        boost::multiprecision::cpp_dec_float_50 pv(nv);

        return new DecimalNumberValue(t, Parser::convertSrcPos(node->pos), nv);
    }

    Value* Parser::parseString(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_String) {
            this->addError("Expected String literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto bstr = BSQON_AST_asLiteralStringNode(node)->data;
        StringValue* svopt = StringValue::createFromParse(t, Parser::convertSrcPos(node->pos), bstr->bytes, bstr->len);

        if(svopt == nullptr) {
            this->addError("Invalid escape characters in string", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return svopt;
    }

    Value* Parser::parseASCIIString(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_ASCIIString) {
            this->addError("Expected ASCIIString literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto bstr = BSQON_AST_asLiteralStringNode(node)->data;
        ASCIIStringValue* svopt = ASCIIStringValue::createFromParse(t, Parser::convertSrcPos(node->pos), bstr->bytes, bstr->len);

        if(svopt == nullptr) {
            this->addError("Invalid escape characters in ascii-string", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return svopt;
    }

    Value* Parser::parseByteBuffer(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_ByteBuffer) {
            this->addError("Expected ByteBuffer literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto buf = BSQON_AST_asLiteralStandardNode(node)->data;
        ByteBufferValue* bvopt = ByteBufferValue::createFromParse(t, Parser::convertSrcPos(node->pos), buf);

        if(bvopt == nullptr) {
            this->addError("Truncated byte value in buffer", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return bvopt;
    }

    Value* Parser::parseUUIDv4(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_UUIDv4) {
            this->addError("Expected UUIDv4 literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto uuid = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        if(!uuid.starts_with("uuid4")) {
            this->addError("Invalid UUIDv4 value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new UUIDv4Value(t, Parser::convertSrcPos(node->pos), uuid.substr(6, uuid.size() - 7));
    }

    Value* Parser::parseUUIDv7(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_UUIDv7) {
            this->addError("Expected UUIDv7 literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto uuid = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        if(!uuid.starts_with("uuid7")) {
            this->addError("Invalid UUIDv7 value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new UUIDv7Value(t, Parser::convertSrcPos(node->pos), uuid.substr(6, uuid.size() - 7));
    }

    Value* Parser::parseSHAHashcode(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_SHAHashcode) {
            this->addError("Expected SHAContentHash literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto hash = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        return new SHAContentHashValue(t, Parser::convertSrcPos(node->pos), hash.substr(4, hash.size() - 5));
    }

    Value* Parser::parseDateTime(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_DateTime) {
            this->addError("Expected DateTime literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto tstr = dstr.substr(dstr.find('T') + 1);
        auto tzstr = dstr.substr(dstr.find('@'));

        uint16_t year;
        uint8_t month, day;
        uint8_t hour, minute, second;
        const char* tz;

        if(!Parser::processDateInfo(dstr, year, month, day) || !Parser::processTimeInfo(tstr, hour, minute, second) || !Parser::processTZInfo(tzstr, &tz)) {
            this->addError("Invalid component in DateTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        DateTime dv = {year, month, day, hour, minute, second, (char*)tz};
        return new DateTimeValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parseUTCDateTime(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_UTCDateTime) {
            this->addError("Expected UTCDateTime literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto tstr = dstr.substr(dstr.find('T') + 1);
        auto tzstr = dstr.substr(dstr.find('@'));

        uint16_t year;
        uint8_t month, day;
        uint8_t hour, minute, second;

        if(!Parser::processDateInfo(dstr, year, month, day) || !Parser::processTimeInfo(tstr, hour, minute, second)) {
            this->addError("Invalid component in UTCDateTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        UTCDateTime dv = {year, month, day, hour, minute, second};
        return new UTCDateTimeValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parsePlainDate(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_PlainDate) {
            this->addError("Expected PlainDate literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);

        uint16_t year;
        uint8_t month, day;

        if(!Parser::processDateInfo(dstr, year, month, day)) {
            this->addError("Invalid component in PlainDate literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        PlainDate dv = {year, month, day};
        return new PlainDateValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parsePlainTime(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_PlainTime) {
            this->addError("Expected PlainTime literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto tstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);

        uint8_t hour, minute, second;

        if(!Parser::processTimeInfo(tstr, hour, minute, second)) {
            this->addError("Invalid component in PlainTime literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        PlainTime dv = {hour, minute, second};
        return new PlainTimeValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parseTickTime(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_TickTime) {
            this->addError("Expected TickTime literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto tstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);

        uint64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 't'

        if(!Parser::isValidWCTime(nv, vv)) {
            this->addError("TickTime value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new TickTimeValue(t, Parser::convertSrcPos(node->pos), vv);
    }

    Value* Parser::parseLogicalTime(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_LogicalTime) {
            this->addError("Expected LogicalTime literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        uint64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'l'

        if(!Parser::isValidWCTime(nv, vv)) {
            this->addError("LogicalTime value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new LogicalTimeValue(t, Parser::convertSrcPos(node->pos), vv);
    }

    Value* Parser::parseISOTimeStamp(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Timestamp) {
            this->addError("Expected ISOTimeStamp literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto tstr = dstr.substr(dstr.find('T') + 1);
        
        uint16_t year;
        uint8_t month, day;
        uint8_t hour, minute, second;
        uint16_t millis;
        
        if(!Parser::processDateInfo(dstr, year, month, day) || !Parser::processTimeInfo(tstr, hour, minute, second) || !Parser::processMillisInfo(tstr, millis)) {
            this->addError("Invalid component in ISOTimeStamp value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        ISOTimeStamp dv = {year, month, day, hour, minute, second, millis};
        return new ISOTimeStampValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parseRegex(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Regex) {
            this->addError("Expected Regex literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto rstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto rri = this->assembly->regexliterals.find(rstr);

        if(rri == this->assembly->regexliterals.end()) {
            this->addError("Invalid Regex value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new RegexValue(t, Parser::convertSrcPos(node->pos), rri->second);
    }

    Value* Parser::parseStringOf(const StringOfType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_StringOf && node->tag != BSQON_AST_TAG_String) {
            this->addError("Expected StringOf literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        const BSQRegex* vre = this->assembly->revalidators.at(t->oftype);

        ByteString* sstr;
        if(node->tag == BSQON_AST_TAG_String) {
            sstr = BSQON_AST_asLiteralStringNode(node)->data;
        }
        else {
            sstr = BSQON_AST_asStringOfNode(node)->data;

            const Type* oftype = this->parseTypeRoot(BSQON_AST_asStringOfNode(node)->type);
            if(oftype->tkey != t->oftype) {
                this->addError("Mismatch between expected StringOf type " + t->oftype + " and given type " + oftype->tkey, Parser::convertSrcPos(node->pos));
            }
        }

        StringOfValue* svopt = StringOfValue::createFromParse(t, Parser::convertSrcPos(node->pos), sstr->bytes, sstr->len, vre);

        if(svopt == nullptr) {
            this->addError("Invalid characters in string (does not validate)", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return svopt;
    }

    Value* Parser::parseASCIIStringOf(const ASCIIStringOfType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_ASCIIStringOf && node->tag != BSQON_AST_TAG_ASCIIString) {
            this->addError("Expected ASCIIStringOf literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        const BSQRegex* vre = this->assembly->revalidators.at(t->oftype);

        ByteString* sstr;
        if(node->tag == BSQON_AST_TAG_ASCIIString) {
            sstr = BSQON_AST_asLiteralStringNode(node)->data;
        }
        else {
            sstr = BSQON_AST_asStringOfNode(node)->data;

            const Type* oftype = this->parseTypeRoot(BSQON_AST_asStringOfNode(node)->type);
            if(oftype->tkey != t->oftype) {
                this->addError("Mismatch between expected ASCIIStringOf type " + t->oftype + " and given type " + oftype->tkey, Parser::convertSrcPos(node->pos));
            }
        }

        ASCIIStringOfValue* svopt = ASCIIStringOfValue::createFromParse(t, Parser::convertSrcPos(node->pos), sstr->bytes, sstr->len, vre);

        if(svopt == nullptr) {
            this->addError("Invalid characters in string (does not validate)", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return svopt;
    }

    Value* Parser::parsePathNaked(const PathType* t, SourcePos spos, BSQON_AST_LiteralStringNode* node)
    {
        const BSQPath* vpath = this->assembly->pthvalidators.at(t->oftype);
        PathValue* popt = PathValue::createFromParse(t, spos, node->data->bytes, node->data->len, vpath);

        if(popt == nullptr) {
            this->addError("Invalid characters in path (does not validate)", spos);
            return new ErrorValue(t, spos);
        }

        return popt;
    }

    Value* Parser::parsePath(const PathType* t, struct BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Path || *BSQON_AST_asPathNode(node)->data->data->bytes != '`') {
            this->addError("Expected Path literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto ptype = this->parseTypeRoot(BSQON_AST_asPathNode(node)->type);
        if(ptype->tkey != t->tkey) {
            this->addError("Mismatch between expected Path type " + t->oftype + " and given type " + ptype->tkey, Parser::convertSrcPos(node->pos));
        }

        return this->parsePathNaked(t, Parser::convertSrcPos(node->pos), BSQON_AST_asPathNode(node)->data);
    }

    Value* Parser::parsePathFragmentNaked(const PathFragmentType* t, SourcePos spos, BSQON_AST_LiteralStringNode* node)
    {
        const BSQPath* vpath = this->assembly->pthvalidators.at(t->oftype);
        PathFragmentValue* popt = PathFragmentValue::createFromParse(t, spos, node->data->bytes, node->data->len, vpath);

        if(popt == nullptr) {
            this->addError("Invalid characters in path (does not validate)", spos);
            return new ErrorValue(t, spos);
        }

        return popt;
    }

    Value* Parser::parsePathFragment(const PathFragmentType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Path || *BSQON_AST_asPathNode(node)->data->data->bytes == 'f') {
            this->addError("Expected PathFragment literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto ptype = this->parseTypeRoot(BSQON_AST_asPathNode(node)->type);
        if(ptype->tkey != t->tkey) {
            this->addError("Mismatch between expected PathFragment type " + t->oftype + " and given type " + ptype->tkey, Parser::convertSrcPos(node->pos));
        }

        return this->parsePathFragmentNaked(t, Parser::convertSrcPos(node->pos), BSQON_AST_asPathNode(node)->data);
    }

    Value* Parser::parsePathGlobNaked(const PathGlobType* t, SourcePos spos, BSQON_AST_LiteralStringNode* node)
    {
        const BSQPath* vpath = this->assembly->pthvalidators.at(t->oftype);
        PathGlobValue* popt = PathGlobValue::createFromParse(t, spos, node->data->bytes, node->data->len, vpath);

        if(popt == nullptr) {
            this->addError("Invalid characters in pathGlob (does not validate)", spos);
            return new ErrorValue(t, spos);
        }

        return popt;
    }

    Value* Parser::parsePathGlob(const PathGlobType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Path || *BSQON_AST_asPathNode(node)->data->data->bytes == 'g') {
            this->addError("Expected PathGlob literal", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto ptype = this->parseTypeRoot(BSQON_AST_asPathNode(node)->type);
        if(ptype->tkey != t->tkey) {
            this->addError("Mismatch between expected PathGlob type " + t->oftype + " and given type " + ptype->tkey, Parser::convertSrcPos(node->pos));
        }

        return this->parsePathGlobNaked(t, Parser::convertSrcPos(node->pos), BSQON_AST_asPathNode(node)->data);
    }

    Value* Parser::parseSomething(const SomethingType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_SomethingCons && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Something value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag == BSQON_AST_TAG_SomethingCons) {
            Value* ofval = this->parseValue(this->assembly->resolveType(t->oftype), BSQON_AST_asSpecialConsNode(node)->value);
            return new SomethingValue(t, Parser::convertSrcPos(node->pos), ofval);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_Nominal) {
                this->addError("Expected Something value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalNode(tnode->type);
            if(oftypenode->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected Something value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }
        
            if(strcmp(oftypenode->name, "Something") != 0) {
                this->addError("Expected Something value but got type " + std::string(oftypenode->name), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
            
            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            std::optional<Value*> ofval = this->processPropertiesForSpecialCons(this->assembly->resolveType(t->oftype), BSQON_AST_asBraceValueNode(tnode->value));
            if(!ofval.has_value()) {
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            return new SomethingValue(t, Parser::convertSrcPos(node->pos), ofval.value());
        }
    }

    Value* Parser::parseOk(const OkType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_OkCons && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Ok value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag == BSQON_AST_TAG_OkCons) {
            Value* ofval = this->parseValue(this->assembly->resolveType(t->ttype), BSQON_AST_asSpecialConsNode(node)->value);
            return new OkValue(t, Parser::convertSrcPos(node->pos), ofval);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_NominalExt) {
                this->addError("Expected Ok value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalExtNode(tnode->type);
            if(oftypenode->root->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected Ok value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }

            if(strcmp(oftypenode->root->name, "Result") != 0 || strcmp(oftypenode->ext, "Ok") != 0) {
                this->addError("Expected Result::Ok value but got type " + std::string(oftypenode->root->name) + "::" + std::string(oftypenode->ext), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
            
            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            std::optional<Value*> ofval = this->processPropertiesForSpecialCons(this->assembly->resolveType(t->ttype), BSQON_AST_asBraceValueNode(tnode->value));
            if(!ofval.has_value()) {
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            return new OkValue(t, Parser::convertSrcPos(node->pos), ofval.value());
        }
    }

    Value* Parser::parseErr(const ErrorType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_ErrCons && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Ok value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag == BSQON_AST_TAG_ErrCons) {
            Value* ofval = this->parseValue(this->assembly->resolveType(t->etype), BSQON_AST_asSpecialConsNode(node)->value);
            return new ErrValue(t, Parser::convertSrcPos(node->pos), ofval);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_NominalExt) {
                this->addError("Expected Err value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalExtNode(tnode->type);
            if(oftypenode->root->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected Err value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }
            
            if(strcmp(oftypenode->root->name, "Result") != 0 || strcmp(oftypenode->ext, "Err") != 0) {
                this->addError("Expected Result::Err value but got type " + std::string(oftypenode->root->name) + "::" + std::string(oftypenode->ext), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            std::optional<Value*> ofval = this->processPropertiesForSpecialCons(this->assembly->resolveType(t->etype), BSQON_AST_asBraceValueNode(tnode->value));
            if(!ofval.has_value()) {
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            return new ErrValue(t, Parser::convertSrcPos(node->pos), ofval.value());
        }
    }

    Value* Parser::parseMapEntry(const MapEntryType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_TypedValue && node->tag != BSQON_AST_TAG_MapEntry) {
            this->addError("Expected MapEntry value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag != BSQON_AST_TAG_MapEntry) {
            auto tnode = BSQON_AST_asMapEntryNode(node);
            auto kv = this->parseValue(this->assembly->resolveType(t->ktype), tnode->key);
            auto vv = this->parseValue(this->assembly->resolveType(t->vtype), tnode->value);

            return new MapEntryValue(t, Parser::convertSrcPos(node->pos), kv, vv);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_Nominal) {
                this->addError("Expected MapEntry value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalNode(tnode->type);
            if(oftypenode->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected MapEntry value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }

            if(strcmp(oftypenode->name, "MapEntry") != 0) {
                this->addError("Expected MapEntry value but got type " + std::string(oftypenode->name), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto vv = this->processPropertiesForMapEntry(this->assembly->resolveType(t->ktype), this->assembly->resolveType(t->vtype), BSQON_AST_asBraceValueNode(tnode->value));
            if(!vv.has_value()) {
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            return new MapEntryValue(t, Parser::convertSrcPos(node->pos), vv.value().first, vv.value().second);
        }
    }
        
    Value* Parser::parseTuple(const TupleType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BracketValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Tuple value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag == BSQON_AST_TAG_TypedValue) {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            const Type* ttype = this->parseTypeRoot(tnode->type);
            if(ttype->tkey != t->tkey) {
                this->addError("Expected " + t->tkey + " value but got " + ttype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BracketValue) {
                this->addError("Expected tuple value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            node = tnode->value;
        }

        auto vvals = this->processEntriesForTuple(t, BSQON_AST_asBracketValueNode(node));
        if(!vvals.has_value()) {
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }
            
        return new TupleValue(t, Parser::convertSrcPos(node->pos), std::move(vvals.value()));
    }

    Value* Parser::parseRecord(const RecordType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BraceValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Record value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag == BSQON_AST_TAG_TypedValue) {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            const Type* ttype = this->parseTypeRoot(tnode->type);
            if(ttype->tkey != t->tkey) {
                this->addError("Expected " + t->tkey + " value but got " + ttype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected record value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            node = tnode->value;
        }

        auto vvals = this->processPropertiesForRecord(t, BSQON_AST_asBraceValueNode(node));
        if(!vvals.has_value()) {
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }
        
        std::vector<Value*> rvals(vvals.value().size(), nullptr);
        std::transform(vvals.value().begin(), vvals.value().end(), rvals.begin(), [](const std::pair<std::string, Value*>& pp) { return pp.second; });

        return new RecordValue(t, Parser::convertSrcPos(node->pos), std::move(rvals));
    }

    Value* Parser::parseEnum(const EnumType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_ScopedName) {
            this->addError("Expected Enum value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto snode = BSQON_AST_asScopedNameNode(node);
        const Type* ttype = this->parseTypeRoot((BSQON_TYPE_AST_Node*)snode->root);
        if(ttype->tkey != t->tkey) {
            this->addError("Expected " + t->tkey + " value but got " + ttype->tkey, Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string ename(snode->identifier);
        auto eiter = std::find(t->variants.cbegin(), t->variants.cend(), ename);

        if(eiter == t->variants.cend()) {
            this->addError("Name " + ename + " not defined in the enumeration", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new EnumValue(t, Parser::convertSrcPos(node->pos), ename, (uint32_t)std::distance(t->variants.cbegin(), eiter));
    }
    
    Value* Parser::parseTypeDecl(const TypedeclType* t, BSQON_AST_Node* node)
    {
        auto vnode = node;
        if(node->tag == BSQON_AST_TAG_TypedLiteral) {
            vnode = BSQON_AST_asTypedLiteralNode(node)->data;
            const Type* tdtype = this->parseTypeRoot(BSQON_AST_asTypedLiteralNode(node)->type);

            if(tdtype->tkey != t->tkey) {
                this->addError("Expected " + t->tkey + " value but got " + tdtype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
        }
        
        const Type* btype = this->assembly->resolveType(t->basetype);
        if(btype->tkey == "None" || btype->tkey == "Nothing") {
            this->addError("Cannot have literal value of none/nothing", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        Value* bval = nullptr;
        if(node->tag == BSQON_AST_TAG_NakedPath) {
            auto npnode = BSQON_AST_asLiteralStringNode(vnode);
            if(*npnode->data->bytes == '`') {
                bval = this->parsePathNaked(static_cast<const PathType*>(btype), Parser::convertSrcPos(vnode->pos), npnode);
            }
            else if(*npnode->data->bytes == 'f') {
                bval = this->parsePathFragmentNaked(static_cast<const PathFragmentType*>(btype), Parser::convertSrcPos(vnode->pos), npnode);
            }
            else {
                bval = this->parsePathGlobNaked(static_cast<const PathGlobType*>(btype), Parser::convertSrcPos(vnode->pos), npnode);
            }
        }
        else {
            bval = this->parseValue(btype, vnode);

            if(bval->vtype->tkey != t->basetype) {
                this->addError("Incompatible value and typedecl -- got " + bval->vtype->tkey + " but expected " + t->basetype, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
        }

        if(!bval->isValidForTypedecl()) {
            this->addError("Value cannot be used in a typedecl " + bval->vtype->tkey, Parser::convertSrcPos(vnode->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new TypedeclValue(t, Parser::convertSrcPos(node->pos), bval);
    }

    Value* Parser::parseStdEntity(const StdEntityType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BraceValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Entity value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag == BSQON_AST_TAG_TypedValue) {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            const Type* ttype = this->parseTypeRoot(tnode->type);
            if(ttype->tkey != t->tkey) {
                this->addError("Expected " + t->tkey + " value but got " + ttype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected entity value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            node = tnode->value;
        }

        auto vvals = this->processPropertiesForEntity(t, BSQON_AST_asBraceValueNode(node));
        if(!vvals.has_value()) {
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }
        
        return new EntityValue(t, Parser::convertSrcPos(node->pos), std::move(vvals.value()));
    }

    Value* Parser::parseList(const ListType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BracketValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected List value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::vector<Value*> vv;
        if(node->tag == BSQON_AST_TAG_BracketValue) {
             this->processEntriesForSequence(t, node, vv);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_Nominal) {
                this->addError("Expected List value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalNode(tnode->type);
            if(oftypenode->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected List value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }

            if(strcmp(oftypenode->name, "List") != 0) {
                this->addError("Expected List value but got type " + std::string(oftypenode->name), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            this->processEntriesForSequence(t, tnode->value, vv);
        }

        return new ListValue(t, Parser::convertSrcPos(node->pos), std::move(vv));
    }

    Value* Parser::parseStack(const StackType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BracketValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Stack value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::vector<Value*> vv;
        if(node->tag == BSQON_AST_TAG_BracketValue) {
             this->processEntriesForSequence(t, node, vv);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_Nominal) {
                this->addError("Expected Stack value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalNode(tnode->type);
            if(oftypenode->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected Stack value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }

            if(strcmp(oftypenode->name, "Stack") != 0) {
                this->addError("Expected Stack value but got type " + std::string(oftypenode->name), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            this->processEntriesForSequence(t, tnode->value, vv);
        }

        return new StackValue(t, Parser::convertSrcPos(node->pos), std::move(vv));
    }

    Value* Parser::parseQueue(const QueueType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BracketValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Queue value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::vector<Value*> vv;
        if(node->tag == BSQON_AST_TAG_BracketValue) {
             this->processEntriesForSequence(t, node, vv);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_Nominal) {
                this->addError("Expected Queue value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalNode(tnode->type);
            if(oftypenode->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected Queue value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }

            if(strcmp(oftypenode->name, "Queue") != 0) {
                this->addError("Expected Queue value but got type " + std::string(oftypenode->name), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            this->processEntriesForSequence(t, tnode->value, vv);
        }

        return new QueueValue(t, Parser::convertSrcPos(node->pos), std::move(vv));
    }

    Value* Parser::parseSet(const SetType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BraceValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Set value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::vector<Value*> vv;
        if(node->tag == BSQON_AST_TAG_BraceValue) {
             this->processEntriesForSequence(t, node, vv);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_Nominal) {
                this->addError("Expected Set value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalNode(tnode->type);
            if(oftypenode->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected Set value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }

            if(strcmp(oftypenode->name, "Set") != 0) {
                this->addError("Expected Set value but got type " + std::string(oftypenode->name), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            this->processEntriesForSequence(t, tnode->value, vv);
        }

        std::sort(vv.begin(), vv.end(), [](const Value* v1, const Value* v2) { return Value::keyCompare(v1, v2) < 0; });
        auto hasdup = std::adjacent_find(vv.cbegin(), vv.cend(), [](const Value* v1, const Value* v2){ return Value::keyCompare(v1, v2) == 0; });
        if(hasdup != vv.cend()) {
            this->addError("Duplicate value in Set", (*(hasdup + 1))->spos);
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new SetValue(t, Parser::convertSrcPos(node->pos), std::move(vv));
    }

    Value* Parser::parseMap(const MapType* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BraceValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected Map value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        const Type* tkey = this->assembly->resolveType(t->ktype);
        const Type* tvalue = this->assembly->resolveType(t->vtype);

        std::vector<MapEntryValue*> vv;
        if(node->tag == BSQON_AST_TAG_BraceValue) {
             this->processEntriesForMap(tkey, tvalue, BSQON_AST_asBraceValueNode(node), vv);
        }
        else {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            if(tnode->type->tag != BSQON_TYPE_AST_TAG_Nominal) {
                this->addError("Expected Map value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            auto oftypenode = BSQON_AST_asNominalNode(tnode->type);
            if(oftypenode->terms != NULL) {
                const Type* ttype = this->parseTypeRoot(tnode->type);
                if(ttype->tkey != t->tkey) {
                    this->addError("Expected Map value but got type " + ttype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
            }

            if(strcmp(oftypenode->name, "Map") != 0) {
                this->addError("Expected Map value but got type " + std::string(oftypenode->name), Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected constructor arg list", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            this->processEntriesForMap(tkey, tvalue, BSQON_AST_asBraceValueNode(tnode->value), vv);
        }

        std::sort(vv.begin(), vv.end(), [](const MapEntryValue* v1, const MapEntryValue* v2) { return Value::keyCompare(v1->key, v2->key) < 0; });
        auto hasdup = std::adjacent_find(vv.cbegin(), vv.cend(), [](const MapEntryValue* v1, const MapEntryValue* v2){ return Value::keyCompare(v1->key, v2->key) == 0; });
        if(hasdup != vv.cend()) {
            this->addError("Duplicate keys in Map", (*(hasdup + 1))->spos);
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new MapValue(t, Parser::convertSrcPos(node->pos), std::move(vv));
    }

    Value* Parser::parseValuePrimitive(const PrimitiveType* t, BSQON_AST_Node* node)
    {
        auto tk = t->tkey;
        if(tk == "None") {
            return this->parseNone(t, node);
        }
        else if(tk == "Nothing") {
            return this->parseNothing(t, node);
        }
        else if(tk == "Bool") {
            return this->parseBool(t, node);
        }
        else if(tk == "Int") {
            return this->parseInt(t, node);
        }
        else if(tk == "Nat") {
            return this->parseNat(t, node);
        }
        else if(tk == "BigInt") {
            return this->parseBigInt(t, node);
        }
        else if(tk == "BigNat") {
            return this->parseBigNat(t, node);
        }
        else if(tk == "Rational") {
            return this->parseRational(t, node);
        }
        else if(tk == "Float") {
            return this->parseFloat(t, node);
        }
        else if(tk == "Decimal") {
            return this->parseDecimal(t, node);
        }
        else if(tk == "String") {
            return this->parseString(t, node);
        }
        else if(tk == "ASCIIString") {
            return this->parseASCIIString(t, node);
        }
        else if(tk == "ByteBuffer") {
            return this->parseByteBuffer(t, node);
        }
        else if(tk == "DateTime") {
            return this->parseDateTime(t, node);
        }
        else if(tk == "UTCDateTime") {
            return this->parseUTCDateTime(t, node);
        }
        else if(tk == "PlainDate") {
            return this->parsePlainDate(t, node);
        }
        else if(tk == "PlainTime") {
            return this->parsePlainTime(t, node);
        }
        else if(tk == "TickTime") {
            return this->parseTickTime(t, node);
        }
        else if(tk == "LogicalTime") {
            return this->parseLogicalTime(t, node);
        }
        else if(tk == "ISOTimeStamp") {
            return this->parseISOTimeStamp(t, node);
        }
        else if(tk == "UUIDv4") {
            return this->parseUUIDv4(t, node);
        }
        else if(tk == "UUIDv7") {
            return this->parseUUIDv7(t, node);
        }
        else if(tk == "SHAContentHash") {
            return this->parseSHAHashcode(t, node);
        } 
        else if(tk == "Regex") {
            return this->parseRegex(t, node);
        }
        else {
            this->addError("Unknown primitive type " + tk, Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }
    }

    Value* Parser::parseValueDirect(const Type* t, BSQON_AST_Node* node)
    {
        switch(t->tag) {
            case TypeTag::TYPE_TUPLE: {
                return this->parseTuple(static_cast<const TupleType*>(t), node);
            }
            case TypeTag::TYPE_RECORD: {
                return this->parseRecord(static_cast<const RecordType*>(t), node);
            }
            case TypeTag::TYPE_STD_ENTITY: {
                return this->parseStdEntity(static_cast<const StdEntityType*>(t), node);
            }
            case TypeTag::TYPE_ENUM: {
                return this->parseEnum(static_cast<const EnumType*>(t), node);
            }
            case TypeTag::TYPE_TYPE_DECL: {
                return this->parseTypeDecl(static_cast<const TypedeclType*>(t), node);
            }
            case TypeTag::TYPE_STRING_OF: {
                return this->parseStringOf(static_cast<const StringOfType*>(t), node);
            }
            case TypeTag::TYPE_ASCII_STRING_OF: {
                return this->parseASCIIStringOf(static_cast<const ASCIIStringOfType*>(t), node);
            }
            case TypeTag::TYPE_SOMETHING: {
                return this->parseSomething(static_cast<const SomethingType*>(t), node);
            }
            case TypeTag::TYPE_OK: {
                return this->parseOk(static_cast<const OkType*>(t), node);
            }
            case TypeTag::TYPE_ERROR: {
                return this->parseErr(static_cast<const ErrorType*>(t), node);
            }
            case TypeTag::TYPE_PATH: {
                return this->parsePath(static_cast<const PathType*>(t), node);
            }
            case TypeTag::TYPE_PATH_FRAGMENT: {
                return this->parsePathFragment(static_cast<const PathFragmentType*>(t), node);
            }
            case TypeTag::TYPE_PATH_GLOB: {
                return this->parsePathGlob(static_cast<const PathGlobType*>(t), node);
            }
            case TypeTag::TYPE_LIST: {
                return this->parseList(static_cast<const ListType*>(t), node);
            }
            case TypeTag::TYPE_STACK: {
                return this->parseStack(static_cast<const StackType*>(t), node);
            }
            case TypeTag::TYPE_QUEUE: {
                return this->parseQueue(static_cast<const QueueType*>(t), node);
            }
            case TypeTag::TYPE_SET: {
                return this->parseSet(static_cast<const SetType*>(t), node);
            }
            case TypeTag::TYPE_MAP_ENTRY: {
                return this->parseMapEntry(static_cast<const MapEntryType*>(t), node);
            }
            case TypeTag::TYPE_MAP: {
                return this->parseMap(static_cast<const MapType*>(t), node);
            }
            default: {
                this->addError("Unknown type " + t->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
        }
    }

    Value* Parser::parseValueConcept(const Type* t, BSQON_AST_Node* node)
    {
        if(t->tag == TypeTag::TYPE_OPTION) {
            const OptionType* otype = static_cast<const OptionType*>(t);
                
            if(node->tag == BSQON_AST_TAG_Nothing) {
                return this->parseNothing(static_cast<const PrimitiveType*>(this->assembly->resolveType("Nothing")), node);
            }
            else {
                return this->parseSomething(static_cast<const SomethingType*>(this->assembly->resolveType("Something<" + otype->oftype + ">")), node);
            }
        }
        else if(t->tag == TypeTag::TYPE_RESULT) {
            const ResultType* rtype = static_cast<const ResultType*>(t);
            const OkType* oktype = static_cast<const OkType*>(this->assembly->resolveType(rtype->tkey + "::Ok"));
            const ErrorType* errtype = static_cast<const ErrorType*>(this->assembly->resolveType(rtype->tkey + "::Err"));

            if(node->tag == BSQON_AST_TAG_OkCons) {
                return this->parseOk(oktype, node);
            }
            else if(node->tag == BSQON_AST_TAG_ErrCons) {
                return this->parseErr(errtype, node);
            }
            else {
                if(node->tag != BSQON_AST_TAG_TypedValue) {
                    this->addError("Values of Result<T, E> type must be tagged", Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }

                const Type* oftype = this->parseTypeRoot(BSQON_AST_asTypedValueNode(node)->type);
                if(oftype->isUnresolved()) {
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }

                if(!this->assembly->checkConcreteSubtype(oftype, t)) {
                    this->addError("Expected result of type " + t->tkey + " but got " + oftype->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }

                if(oftype->tag == TypeTag::TYPE_OK) {
                    return this->parseOk(static_cast<const OkType*>(oftype), node);
                }
                else {
                    return this->parseErr(static_cast<const ErrorType*>(errtype), node);
                }
            }
        }
        else if(t->tag == TypeTag::TYPE_STD_CONCEPT || t->tag == TypeTag::TYPE_CONCEPT_SET) {
            if(node->tag != BSQON_AST_TAG_TypedValue) {
                this->addError("Values of Concept type must be tagged", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            const Type* oftype = this->parseTypeRoot(BSQON_AST_asTypedValueNode(node)->type);
            if(oftype->isUnresolved()) {
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(!this->assembly->checkConcreteSubtype(oftype, t)) {
                this->addError("Expected result of type " + t->tkey + " but got " + oftype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
            
            return this->parseStdEntity(static_cast<const StdEntityType*>(oftype), node);
        }
        else {
            this->addError("Unknown type " + t->tkey, Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }
    }

    Value* Parser::parseValueSimple(const Type* t, BSQON_AST_Node* node)
    {
        if (t->tag == TypeTag::TYPE_PRIMITIVE) {
            return this->parseValuePrimitive(static_cast<const PrimitiveType*>(t), node);
        }
        else if ((t->tag == TypeTag::TYPE_STD_CONCEPT) || (t->tag == TypeTag::TYPE_CONCEPT_SET)) {
            return this->parseValueConcept(t, node);
        }
        else {
            return this->parseValueDirect(t, node);
        }
    }

    Value* Parser::parseValueUnion(const UnionType* t, BSQON_AST_Node* node)
    {
        //everyone has a none special format option
        if(node->tag == BSQON_AST_TAG_None) {
            if(std::find(t->types.cbegin(), t->types.cend(), "None") == t->types.cend()) {
                this->addError("Expected result of type " + t->tkey + " but got none", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            return this->parseNone(static_cast<const PrimitiveType*>(this->assembly->resolveType("None")), node);
        }

        //Check for special nonable form as well "T | none"
        if(this->isNoneableParse(t)) {
            //from previous check we know that the type is not none
            return this->parseValueSimple(this->getNoneableRealType(t), node);
        }

        //it isn't none so now we start looking at tags
        auto tk = node->tag;
        Value* vv = nullptr;
        const Type* tt = nullptr;
        if(tk == BSQON_AST_TAG_TypedValue) {
            tt = this->parseTypeRoot(BSQON_AST_asTypedValueNode(node)->type);
            if(std::find(s_okTypeTaggedTags.cbegin(), s_okTypeTaggedTags.cend(), tt->tag) == s_okTypeTaggedTags.cend()) {
                this->addError("Invalid tagged value " + tt->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
            vv = this->parseValueDirect(tt, BSQON_AST_asTypedValueNode(node)->value);
        }
        else if(tk == BSQON_AST_TAG_StringOf) {
            const Type* oftype = this->parseTypeRoot(BSQON_AST_asStringOfNode(node)->type);
            if(oftype->isUnresolved()) {
                this->addError("Invalid StringOf value " + oftype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            tt = this->assembly->resolveType("StringOf<" + oftype->tkey + ">");
            if(tt->tag != TypeTag::TYPE_STRING_OF) {
                this->addError("Invalid StringOf  value " + tt->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
            vv = this->parseStringOf(static_cast<const StringOfType*>(tt), node);
        }
        else if(tk == BSQON_AST_TAG_ASCIIStringOf) {
            const Type* oftype = this->parseTypeRoot(BSQON_AST_asStringOfNode(node)->type);
            if(oftype->isUnresolved()) {
                this->addError("Invalid ASCIIStringOf value " + oftype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            tt = this->assembly->resolveType("ASCIIStringOf<" + oftype->tkey + ">");
            if(tt->tag != TypeTag::TYPE_ASCII_STRING_OF) {
                this->addError("Invalid ASCIIStringOf value " + tt->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
            vv = this->parseASCIIStringOf(static_cast<const ASCIIStringOfType*>(tt), node);
        }
        else if(tk == BSQON_AST_TAG_Path) {
            auto pnode = BSQON_AST_asPathNode(node);

            const Type* oftype = this->parseTypeRoot(pnode->type);
            if(oftype->isUnresolved()) {
                this->addError("Invalid path value " + oftype->tkey, Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            char pfx = *pnode->data->data->bytes;
            if(pfx == 'g') {
                tt = this->assembly->resolveType("PathGlob<" + oftype->tkey + ">");
                if(tt->tag != TypeTag::TYPE_PATH_GLOB) {
                    this->addError("Invalid PathGlob value " + tt->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
                vv = this->parsePathGlob(static_cast<const PathGlobType*>(tt), node);
            }
            else if(pfx == 'f') {
                tt = this->assembly->resolveType("PathFragment<" + oftype->tkey + ">");
                if(tt->tag != TypeTag::TYPE_PATH_FRAGMENT) {
                    this->addError("Invalid PathFragment value " + tt->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
                vv = this->parsePathFragment(static_cast<const PathFragmentType*>(tt), node);
            }
            else {
                tt = this->assembly->resolveType("Path<" + oftype->tkey + ">");
                if(tt->tag != TypeTag::TYPE_PATH) {
                    this->addError("Invalid Path value " + tt->tkey, Parser::convertSrcPos(node->pos));
                    return new ErrorValue(t, Parser::convertSrcPos(node->pos));
                }
                vv = this->parsePath(static_cast<const PathType*>(tt), node);
            }
        }
        else if(tk == BSQON_AST_TAG_TypedLiteral) {
            tt = this->parseTypeRoot(BSQON_AST_asTypedLiteralNode(node)->type);
            if(tt->isUnresolved()) {
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            vv = this->parseValueSimple(tt, BSQON_AST_asTypedLiteralNode(node)->data);
        }
        else {
            if(tk == BSQON_AST_TAG_True || tk == BSQON_AST_TAG_False) {
                tt = this->assembly->resolveType("Bool");
                vv = this->parseBool(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_Nat) {
                tt = this->assembly->resolveType("Nat");
                vv = this->parseNat(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_Int) {
                tt = this->assembly->resolveType("Int");
                vv = this->parseInt(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_BigNat) {
                tt = this->assembly->resolveType("BigNat");
                vv = this->parseBigNat(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_BigInt) {
                tt = this->assembly->resolveType("BigInt");
                vv = this->parseBigInt(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_Float) {
                tt = this->assembly->resolveType("Float");
                vv = this->parseFloat(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_Decimal) {
                tt = this->assembly->resolveType("Decimal");
                vv = this->parseDecimal(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_Rational) {
                tt = this->assembly->resolveType("Rational");
                vv = this->parseRational(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_String) {
                tt = this->assembly->resolveType("String");
                vv = this->parseString(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_ASCIIString) {
                tt = this->assembly->resolveType("ASCIIString");
                vv = this->parseASCIIString(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_ByteBuffer) {
                tt = this->assembly->resolveType("ByteBuffer");
                vv = this->parseByteBuffer(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_Regex) {
                tt = this->assembly->resolveType("Regex");
                vv = this->parseRegex(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_DateTime) {
                tt = this->assembly->resolveType("DateTime");
                vv = this->parseDateTime(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_UTCDateTime) {
                tt = this->assembly->resolveType("UTCDateTime");
                vv = this->parseUTCDateTime(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_PlainDate) {
                tt = this->assembly->resolveType("PlainDate");
                vv = this->parsePlainDate(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_PlainTime) {
                tt = this->assembly->resolveType("PlainTime");
                vv = this->parsePlainTime(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_TickTime) {
                tt = this->assembly->resolveType("TickTime");
                vv = this->parseTickTime(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_LogicalTime) {
                tt = this->assembly->resolveType("LogicalTime");
                vv = this->parseLogicalTime(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_Timestamp) {
                tt = this->assembly->resolveType("ISOTimeStamp");
                vv = this->parseISOTimeStamp(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_UUIDv4) {
                tt = this->assembly->resolveType("UUIDv4");
                vv = this->parseUUIDv4(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_UUIDv7) {
                tt = this->assembly->resolveType("UUIDv7");
                vv = this->parseUUIDv7(static_cast<const PrimitiveType*>(tt), node);
            }
            else if(tk == BSQON_AST_TAG_SHAHashcode) {
                tt = this->assembly->resolveType("SHAContentHash");
                vv = this->parseSHAHashcode(static_cast<const PrimitiveType*>(tt), node);
            }
            else {
                this->addError("Cannot implicitly resolve ", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }
        }

        if(!this->assembly->checkConcreteSubtype(tt, t)) {
            this->addError("Expected result of type " + t->tkey + " but got " + tt->tkey, Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }
            
        return vv;
    }

    Value* Parser::parseIdentifier(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Identifier) {
            this->addError("Expected Identifier value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string vname = BSQON_AST_asNameNode(node)->data;
        if(!this->vbinds.contains(vname)) {
            this->addError("Unknown let binding " + vname, Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        const Type* oftype = this->vbinds[vname]->vtype;

        if(oftype->isUnresolved()) {
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(!this->assembly->checkConcreteSubtype(oftype, t)) {
            this->addError("Expected result of type " + t->tkey + " but got " + oftype->tkey, Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return this->vbinds[vname];
    }

    Value* Parser::parseLetIn(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_LetIn) {
            this->addError("Expected LetIn value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto lnode = BSQON_AST_asLetInNode(node);

        std::string vname = lnode->vname;
        if(this->vbinds.contains(vname)) {
            this->addError("Duplicate let binding " + vname, Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        const Type* vtype = this->parseTypeRoot(lnode->vtype);
        if(vtype->isUnresolved()) {
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        Value* vvalue = this->parseValue(vtype, lnode->value);
        this->vbinds[vname] = vvalue;

        Value* res = this->parseValue(t, lnode->exp);

        this->vbinds.erase(vname);
        return res;
    }

    Value* Parser::parseValue(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag == BSQON_AST_TAG_Identifier) {
            return this->parseIdentifier(t, node);
        }
        else if(node->tag == BSQON_AST_TAG_LetIn) {
            return this->parseLetIn(t, node);
        }
        else {
            if (t->tag == TypeTag::TYPE_UNION) {
                return this->parseValueUnion(static_cast<const UnionType*>(t), node);
            }
            else {
                return this->parseValueSimple(t, node);
            }
        }
    }
}

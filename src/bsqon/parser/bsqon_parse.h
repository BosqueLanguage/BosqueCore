#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"
#include "../regex/bsqpath.h"

#include "../info/type_info.h"
#include "../info/bsqon.h"

#include "lb/bsqon_type_ast.h"
#include "lb/bsqon_ast.h"

namespace BSQON
{
    class ParseError
    {
    public:
        std::string message;
        SourcePos loc;

        ParseError(std::string message, SourcePos loc) : message(message), loc(loc) {;}
    };

    class Parser
    {
    private:
        static SourcePos convertSrcPos(struct AST_SourcePos spos)
        {
            return SourcePos(spos.first_line, spos.first_column, spos.last_line, spos.last_column);
        }

        void addError(std::string message, SourcePos loc)
        {
            this->errors.push_back(ParseError(message, loc));
        }

        static bool isValidNat(const std::string nv, int64_t& vv);
        static bool isValidInt(const std::string nv, int64_t& vv);
        static bool isValidWCTime(const std::string nv, uint64_t& vv);

        static bool processDateInfo(const std::string& ds, uint16_t& yy, uint8_t& mm, uint8_t& dd);
        static bool processTimeInfo(const std::string& ds, uint8_t& hh, uint8_t& mm, uint8_t& ss);
        static bool processMillisInfo(const std::string& ds, uint16_t& millis);

        bool processTZInfo(const std::string& ds, const char** tz);
        
        std::vector<std::pair<std::string, Value*>> processPropertiesForRecord(const RecordType* ttype, struct BSQON_AST_BraceValueNode* node);
        std::vector<Value*> processPropertiesForEntity(const StdEntityType* ttype, struct BSQON_AST_BraceValueNode* node);

        std::vector<Value*> processPropertiesForSequence(const Type* etype, struct BSQON_AST_BracketValueNode* node);
        std::vector<Value*> processPropertiesForMap(const Type* keytype, const Type* valtype, struct BSQON_AST_BraceValueNode* node);

    public:
        const AssemblyInfo* assembly;

        const std::string defaultns;
        std::map<std::string, std::string> importmap;
        std::set<std::string> tzset;

        std::vector<ParseError> errors;

        Parser(const AssemblyInfo* assembly) {;}
        virtual ~Parser() = default;

        const Type* resolveTypeFromNameList(std::string basenominal, std::vector<const Type*> terms);
        const Type* resolveAndCheckType(TypeKey tkey, SourcePos spos);

        const Type* processCoreType(std::string tname);

        bool parseTemplateTermList(struct BSQON_TYPE_AST_List* tlist, std::vector<const Type*>& terms);
        const Type* parseTemplateTermList_One(SourcePos spos, struct BSQON_TYPE_AST_List* tlist); 
        std::pair<const Type*, const Type*> parseTemplateTermList_Two(SourcePos spos, struct BSQON_TYPE_AST_List* tlist);

        const Type* parseTemplateTypeHelper_One(std::string sname, SourcePos spos, struct BSQON_TYPE_AST_List* tlist);
        const Type* parseTemplateTypeHelper_Two(std::string sname, SourcePos spos, struct BSQON_TYPE_AST_List* tlist);

        const Type* parseTemplateTypeHelper_OkErr(const Type* tresult, std::string sname, SourcePos spos);

        const Type* parseStringOfType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("StringOf", spos, tlist);
        }

        const Type* parseASCIIStringOfType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("ASCIIStringOf", spos, tlist);
        }

        const Type* parseSomethingType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("Something", spos, tlist);
        }

        const Type* parseOptionType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("Option", spos, tlist);
        }

        const Type* parseResultType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_Two("Result", spos, tlist);
        }

        const Type* parsePathType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("Path", spos, tlist);
        }

        const Type* parsePathFragmentType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("PathFragment", spos, tlist);
        }

        const Type* parsePathGlobType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("PathGlob", spos, tlist);
        }

        const Type* parseListType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("List", spos, tlist);
        }

        const Type* parseStackType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("Stack", spos, tlist);
        }

        const Type* parseQueueType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("Queue", spos, tlist);
        }

        const Type* parseSetType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_One("Set", spos, tlist);
        }

        const Type* parseMapEntryType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_Two("MapEntry", spos, tlist);
        }

        const Type* parseMapType(SourcePos spos, struct BSQON_TYPE_AST_List* tlist)
        {
            return this->parseTemplateTypeHelper_Two("Map", spos, tlist);
        }

        const Type* parseNominalType(struct BSQON_TYPE_AST_NominalNode* node);
        const Type* parseNominalTemplateType(struct BSQON_TYPE_AST_NominalExtNode* node);
        const Type* parseTupleType(struct BSQON_TYPE_AST_TupleNode* node);
        const Type* parseRecordType(struct BSQON_TYPE_AST_RecordNode* node);
        const Type* parseConceptSetType(struct BSQON_TYPE_AST_Conjunction* node);
        const Type* parseUnionType(struct BSQON_TYPE_AST_Union* node);
        const Type* parseType(struct BSQON_TYPE_AST_Node* node);

        const Type* parseTypeRoot(struct BSQON_TYPE_AST_Node* node);

        Value* parseNone(const Type* t, struct BSQON_AST_Node* node);
        Value* parseNothing(const Type* t, struct BSQON_AST_Node* node);

        Value* parseBool(const Type* t, struct BSQON_AST_Node* node);
        Value* parseNat(const Type* t, struct BSQON_AST_Node* node);
        Value* parseInt(const Type* t, struct BSQON_AST_Node* node);
        Value* parseBigNat(const Type* t, struct BSQON_AST_Node* node);
        Value* parseBigInt(const Type* t, struct BSQON_AST_Node* node);

        Value* parseRational(const Type* t, struct BSQON_AST_Node* node);
        Value* parseFloat(const Type* t, struct BSQON_AST_Node* node);
        Value* parseDecmial(const Type* t, struct BSQON_AST_Node* node);

        Value* parseString(const Type* t, struct BSQON_AST_Node* node);
        Value* parseASCIIString(const Type* t, struct BSQON_AST_Node* node);
        Value* parseByteBuffer(const Type* t, struct BSQON_AST_Node* node);
        Value* parseUUIDv4(const Type* t, struct BSQON_AST_Node* node);
        Value* parseUUIDv7(const Type* t, struct BSQON_AST_Node* node);
        Value* parseSHAHashcode(const Type* t, struct BSQON_AST_Node* node);

        Value* parseDateTime(const Type* t, struct BSQON_AST_Node* node);
        Value* parseUTCDateTime(const Type* t, struct BSQON_AST_Node* node);
        Value* parsePlainDate(const Type* t, struct BSQON_AST_Node* node);
        Value* parsePlainTime(const Type* t, struct BSQON_AST_Node* node);
        Value* parseTickTime(const Type* t, struct BSQON_AST_Node* node);
        Value* parseLogicalTime(const Type* t, struct BSQON_AST_Node* node);
        Value* parseISOTimeStamp(const Type* t, struct BSQON_AST_Node* node);

        Value* parseRegex(const Type* t, struct BSQON_AST_Node* node);

        Value* parseLatLongCoordinate(const Type* t, struct BSQON_AST_Node* node);

        Value* parseStringOf(const Type* t, struct BSQON_AST_Node* node);
        Value* parseASCIIStringOf(const Type* t, struct BSQON_AST_Node* node);
    };
}

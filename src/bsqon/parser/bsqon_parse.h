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
        
    public:
        const AssemblyInfo* assembly;
        std::set<std::string> tzset;

        std::vector<ParseError> errors;

        Parser(const AssemblyInfo* assembly) {;}
        virtual ~Parser() = default;

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

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

    public:
        const AssemblyInfo* assembly;
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
    };
}

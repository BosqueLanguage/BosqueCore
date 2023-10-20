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

    public:
        const AssemblyInfo* assembly;
        std::vector<ParseError> errors;

        Parser(const AssemblyInfo* assembly) {;}
        virtual ~Parser() = default;

        NoneValue* parseNone(const Type* t, struct BSQON_AST_Node* node);
        NothingValue* parseNothing(const Type* t, struct BSQON_AST_Node* node);

        BoolValue* parseBool(const Type* t, struct BSQON_AST_Node* node);
        NatNumberValue* parseNat(const Type* t, struct BSQON_AST_Node* node);
        IntNumberValue* parseInt(const Type* t, struct BSQON_AST_Node* node);
        NatNumberValue* parseBigNat(const Type* t, struct BSQON_AST_Node* node);
        IntNumberValue* parseBigInt(const Type* t, struct BSQON_AST_Node* node);

        RationalNumberValue* parseRational(const Type* t, struct BSQON_AST_Node* node);
        FloatNumberValue* parseFloat(const Type* t, struct BSQON_AST_Node* node);
        FloatNumberValue* parseDecmial(const Type* t, struct BSQON_AST_Node* node);
    };
}

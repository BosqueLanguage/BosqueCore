#include "bsqon_parse.h"

BSQON::NoneValue* BSQON::Parser::parseNone(const BSQON::Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_None) {
        throw std::runtime_error("Expected None value");
    }

    return new NoneValue(t, Parser::convertSrcPos(node->pos));
}
    
    NothingValue* Parser::parseNothing(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    BoolValue* Parser::parseBool(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    NatNumberValue* Parser::parseNat(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    IntNumberValue* Parser::parseInt(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    NatNumberValue* Parser::parseBigNat(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    IntNumberValue* Parser::parseBigInt(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    RationalNumberValue* Parser::parseRational(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    FloatNumberValue* Parser::parseFloat(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

    FloatNumberValue* Parser::parseDecmial(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

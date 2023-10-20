#include "bsqon_parse.h"

#include <inttypes.h>

bool BSQON::Parser::isValidNat(const std::string nv, int64_t& vv)
{
    auto ecount = sscanf(nv.c_str(), "%" SCNd64, vv);
    return ecount == 1 && 0 <= vv && vv <= Type::MAX_SAFE_NUMBER; 
}

bool BSQON::Parser::isValidInt(const std::string nv, int64_t& vv)
{
    auto ecount = sscanf(nv.c_str(), "%" SCNd64, vv);
    return ecount == 1 && Type::MIN_SAFE_NUMBER <= vv && vv <= Type::MAX_SAFE_NUMBER;
}

BSQON::Value* BSQON::Parser::parseNone(const Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_None) {
        this->addError("Expected None value", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    return new NoneValue(t, Parser::convertSrcPos(node->pos));
}
    
BSQON::Value* BSQON::Parser::parseNothing(const Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_Nothing) {
        this->addError("Expected Nothing value", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    return new NothingValue(t, Parser::convertSrcPos(node->pos));
}

BSQON::Value* BSQON::Parser::parseBool(const Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_True && node->tag != BSQON_AST_TAG_False) {
        this->addError("Expected Boolean value", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    return new BoolValue(t, Parser::convertSrcPos(node->pos), node->tag == BSQON_AST_TAG_True);
}

BSQON::Value* BSQON::Parser::parseNat(const Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_Nat) {
        this->addError("Expected Nat value", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    int64_t vv;
    std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
    nv.pop_back(); //remove the trailing 'n'

    if(!Parser::isValidNat(nv, vv)) {
        this->addError("Nat value could not be parsed", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    return new NatNumberValue(t, Parser::convertSrcPos(node->pos), std::make_optional((uint64_t)vv), nv);
}

BSQON::Value* BSQON::Parser::parseInt(const Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_Int) {
        this->addError("Expected Int value", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    int64_t vv;
    std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
    nv.pop_back(); //remove the trailing 'i'

    if(!Parser::isValidInt(nv, vv)) {
        this->addError("Int value could not be parsed", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    return new IntNumberValue(t, Parser::convertSrcPos(node->pos), std::make_optional(vv), nv);
}

BSQON::Value* BSQON::Parser::parseBigNat(const Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_BigNat) {
        this->addError("Expected BigNat value", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    int64_t vv;
    std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
    nv.pop_back(); //remove the trailing 'N'

    bool smallv = Parser::isValidNat(nv, vv);

    return new NatNumberValue(t, Parser::convertSrcPos(node->pos), smallv ? std::make_optional((uint64_t)vv) : std::nullopt, std::string(BSQON_AST_asLiteralStandardNode(node)->data));
}

BSQON::Value* BSQON::Parser::parseBigInt(const Type* t, struct BSQON_AST_Node* node)
{
    if(node->tag != BSQON_AST_TAG_BigInt) {
        this->addError("Expected BigInt value", Parser::convertSrcPos(node->pos));
        return new ErrorValue(t, Parser::convertSrcPos(node->pos));
    }

    int64_t vv;
    std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
    nv.pop_back(); //remove the trailing 'I'

    bool smallv = Parser::isValidNat(nv, vv);

    return new IntNumberValue(t, Parser::convertSrcPos(node->pos), smallv ? std::make_optional(vv) : std::nullopt, std::string(BSQON_AST_asLiteralStandardNode(node)->data));
}

BSQON::Value* BSQON::Parser::parseRational(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

BSQON::Value* BSQON::Parser::parseFloat(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

BSQON::Value* BSQON::Parser::parseDecmial(const Type* t, struct BSQON_AST_Node* node)
    {
        xxxx;
    }

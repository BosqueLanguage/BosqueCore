#pragma once

#include "bytestring.h"

enum BSQON_AST_TAG
{
    BSQON_AST_TAG_None = 1,
    BSQON_AST_TAG_Nothing,
    BSQON_AST_TAG_True,
    BSQON_AST_TAG_False,
    BSQON_AST_TAG_Nat,
    BSQON_AST_TAG_Int,
    BSQON_AST_TAG_BigNat,
    BSQON_AST_TAG_BigInt,
    BSQON_AST_TAG_Rational,
    BSQON_AST_TAG_Float,
    BSQON_AST_TAG_Double,
    BSQON_AST_TAG_Numberino,
    BSQON_AST_TAG_ByteBuffer,
    BSQON_AST_TAG_UUIDv4,
    BSQON_AST_TAG_UUIDv7,
    BSQON_AST_TAG_SHAHashcode,
    BSQON_AST_TAG_String,
    BSQON_AST_TAG_ASCIIString,
    BSQON_AST_TAG_Regex,
    BSQON_AST_TAG_PathItem,
    BSQON_AST_TAG_DateTime,
    BSQON_AST_TAG_UTCDateTime,
    BSQON_AST_TAG_PlainDate,
    BSQON_AST_TAG_PlainTime,
    BSQON_AST_TAG_LogicalTime,
    BSQON_AST_TAG_TickTime,
    BSQON_AST_TAG_Timestamp,

    BSQON_AST_TAG_Identifier,
    BSQON_AST_TAG_UnspecIdentifier
};

struct BSQON_AST_Node
{
    enum BSQON_AST_TAG tag;
};

struct BSQON_AST_LiteralNode
{
    struct BSQON_AST_Node base;
    struct ByteString data;
};

struct BSQON_AST_NameNode
{
    //Identifier | UnspecIdentifier | TypeComponent
    struct BSQON_AST_Node base;
    struct ByteString data;
};

enum BSQON_AST_TAG BSQON_AST_getTag(const struct BSQON_AST_Node* node);
void BSQON_AST_print(struct BSQON_AST_Node* node);

struct BSQON_AST_LiteralNode* BSQON_AST_asLiteralNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_LiteralNodeCreateEmpty(enum BSQON_AST_TAG tag);
struct BSQON_AST_Node* BSQON_AST_LiteralNodeCreateChars(enum BSQON_AST_TAG tag, const char* data);
struct BSQON_AST_Node* BSQON_AST_LiteralNodeCreateBytes(enum BSQON_AST_TAG tag, struct ByteString* data);
void BSQON_AST_LiteralNode_print(struct BSQON_AST_LiteralNode* node);

//Identifier | UnspecIdentifier | TypeComponent
struct BSQON_AST_NameNode* BSQON_AST_asNameNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_NameNodeCreate(enum BSQON_AST_TAG tag, const char* data);
void BSQON_AST_NameNode_print(struct BSQON_AST_NameNode* node);
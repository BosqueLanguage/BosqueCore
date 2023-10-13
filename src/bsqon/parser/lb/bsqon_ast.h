#pragma once

#include "bytestring.h"
#include "bsqon_type_ast.h"

enum BSQON_AST_TAG
{
    BSQON_AST_TAG_Error = 1,
    BSQON_AST_TAG_None,
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
    BSQON_AST_TAG_DateTime,
    BSQON_AST_TAG_UTCDateTime,
    BSQON_AST_TAG_PlainDate,
    BSQON_AST_TAG_PlainTime,
    BSQON_AST_TAG_LogicalTime,
    BSQON_AST_TAG_TickTime,
    BSQON_AST_TAG_Timestamp,

    BSQON_AST_TAG_Identifier,
    BSQON_AST_TAG_UnspecIdentifier,
    
    BSQON_AST_TAG_StringOf,
    BSQON_AST_TAG_ASCIIStringOf,
    BSQON_AST_TAG_Path,
    BSQON_AST_TAG_TypedLiteral
};

struct BSQON_AST_Node
{
    enum BSQON_AST_TAG tag;
};

struct BSQON_AST_List
{
    struct BSQON_AST_Node* value;
    struct BSQON_AST_List* next;
};

struct BSQON_AST_NamedListEntry
{
    const char* name;
    struct BSQON_AST_Node* value;
};

struct BSQON_AST_NamedList
{
    struct BSQON_AST_NamedListEntry* value;
    struct BSQON_AST_NamedList* next;
};

struct BSQON_AST_ErrorNode
{
    struct BSQON_AST_Node base;
};

struct BSQON_AST_LiteralSingletonNode
{
    struct BSQON_AST_Node base;
};

struct BSQON_AST_LiteralStringNode
{
    struct BSQON_AST_Node base;
    struct ByteString* data;
};

struct BSQON_AST_LiteralStandardNode
{
    struct BSQON_AST_Node base;
    const char* data;
};

struct BSQON_AST_NameNode
{
    //Identifier | UnspecIdentifier
    struct BSQON_AST_Node base;
    const char* data;
};

struct BSQON_AST_StringOfNode
{
    struct BSQON_AST_Node base;
    struct ByteString* data;
    struct BSQON_TYPE_AST_Node* type;
};

struct BSQON_AST_PathNode
{
    struct BSQON_AST_Node base;
    struct ByteString* data;
    struct BSQON_TYPE_AST_Node* type;
};

struct BSQON_AST_TypedLiteralNode
{
    struct BSQON_AST_Node base;
    struct BSQON_AST_Node* data; //Singleton | String | Standard
    struct BSQON_TYPE_AST_Node* type;
};

struct BSQON_AST_List* BSQON_AST_ListCons(struct BSQON_AST_Node* value, struct BSQON_AST_List* next);
struct BSQON_AST_List* BSQON_AST_ListCompleteParse(struct BSQON_AST_List* ll);

struct BSQON_AST_NamedListEntry* BSQON_AST_NamedListEntryCreate(const char* name, struct BSQON_AST_Node* value);
struct BSQON_AST_NamedList* BSQON_AST_NamedListCons(struct BSQON_AST_NamedListEntry* value, struct BSQON_TYPE_AST_NamedList* next);
struct BSQON_AST_NamedList* BSQON_AST_NamedListCompleteParse(struct BSQON_AST_NamedList* ll);

enum BSQON_AST_TAG BSQON_AST_getTag(const struct BSQON_AST_Node* node);
void BSQON_AST_print(struct BSQON_AST_Node* node);

struct BSQON_AST_Node* BSQON_AST_ErrorNodeCreate();

struct BSQON_AST_LiteralSingletonNode* BSQON_AST_asLiteralSingletonNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_LiteralSingletonNodeCreate(enum BSQON_AST_TAG tag);

struct BSQON_AST_LiteralStringNode* BSQON_AST_asLiteralStringNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_LiteralStringNodeCreate(enum BSQON_AST_TAG tag, struct ByteString* data);
void BSQON_AST_LiteralStringNode_print(struct BSQON_AST_LiteralStringNode* node);

struct BSQON_AST_LiteralStandardNode* BSQON_AST_asLiteralStandardNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_LiteralStandardNodeCreate(enum BSQON_AST_TAG tag, const char* data);
void BSQON_AST_LiteralStandardNode_print(struct BSQON_AST_LiteralStandardNode* node);

//Identifier | UnspecIdentifier | TypeComponent
struct BSQON_AST_NameNode* BSQON_AST_asNameNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_NameNodeCreate(enum BSQON_AST_TAG tag, const char* data);
void BSQON_AST_NameNode_print(struct BSQON_AST_NameNode* node);

struct BSQON_AST_StringOfNode* BSQON_AST_asStringOfNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_StringOfNodeCreate(enum BSQON_AST_TAG tag, struct ByteString* str, struct BSQON_TYPE_AST_Node* type);
void BSQON_AST_StringOfNode_print(struct BSQON_AST_StringOfNode* node);

struct BSQON_AST_PathNode* BSQON_AST_asPathNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_PathNodeCreate(struct ByteString* str, struct BSQON_TYPE_AST_Node* type);
void BSQON_AST_PathNode_print(struct BSQON_AST_PathNode* node);

struct BSQON_AST_TypedLiteralNode* BSQON_AST_asTypedLiteralNode(const struct BSQON_AST_Node* node);
struct BSQON_AST_Node* BSQON_AST_TypedLiteralNodeCreate(struct BSQON_AST_Node* data, struct BSQON_TYPE_AST_Node* type);
void BSQON_AST_TypedLiteralNode_print(struct BSQON_AST_TypedLiteralNode* node);

#pragma once

#include "bytestring.h"

enum BSQON_TYPE_AST_TAG
{
    BSQON_TYPE_AST_TAG_Error = 1,
    BSQON_TYPE_AST_TAG_Nominal,
    BSQON_TYPE_AST_TAG_NominalExt,
    BSQON_TYPE_AST_TAG_Tuple,
    BSQON_TYPE_AST_TAG_Record,
    BSQON_TYPE_AST_TAG_Conjunction,
    BSQON_TYPE_AST_TAG_Union
};

struct BSQON_TYPE_AST_Node
{
    enum BSQON_TYPE_AST_TAG tag;
};

struct BSQON_TYPE_AST_List
{
    struct BSQON_TYPE_AST_Node* value;
    struct BSQON_TYPE_AST_List* next;
};

struct BSQON_TYPE_AST_NamedListEntry
{
    const char* name;
    struct BSQON_TYPE_AST_Node* value;
};

struct BSQON_TYPE_AST_NamedList
{
    struct BSQON_TYPE_AST_NamedListEntry* value;
    struct BSQON_TYPE_AST_NamedList* next;
};

struct BSQON_TYPE_AST_ErrorNode
{
    struct BSQON_TYPE_AST_Node base;
};

struct BSQON_TYPE_AST_NominalNode
{
    struct BSQON_TYPE_AST_Node base;
    const char* name;
    struct BSQON_TYPE_AST_List* terms;
};

struct BSQON_TYPE_AST_NominalExtNode
{
    struct BSQON_TYPE_AST_Node base;
    struct BSQON_TYPE_AST_NominalNode* root;
    struct ByteString ext;
};

struct BSQON_TYPE_AST_TupleNode
{
    struct BSQON_TYPE_AST_Node base;
    struct BSQON_TYPE_AST_List* types;
};

struct BSQON_TYPE_AST_RecordNode
{
    struct BSQON_TYPE_AST_Node base;
    struct BSQON_TYPE_AST_NamedList* entries;
};

struct BSQON_TYPE_AST_Conjunction
{
    struct BSQON_TYPE_AST_Node base;
    struct BSQON_TYPE_AST_Node* left;
    struct BSQON_TYPE_AST_Node* right;
};

struct BSQON_TYPE_AST_Union
{
    struct BSQON_TYPE_AST_Node base;
    struct BSQON_TYPE_AST_Node* left;
    struct BSQON_TYPE_AST_Node* right;
};

struct BSQON_TYPE_AST_List* BSQON_TYPE_AST_ListCons(struct BSQON_TYPE_AST_Node* value, struct BSQON_TYPE_AST_List* next);
struct BSQON_TYPE_AST_List* BSQON_TYPE_AST_ListCompleteParse(struct BSQON_TYPE_AST_List* ll);

struct BSQON_TYPE_AST_NamedListEntry* BSQON_TYPE_AST_NamedListEntryCreate(const char* name, struct BSQON_TYPE_AST_Node* value);
struct BSQON_TYPE_AST_NamedList* BSQON_TYPE_AST_NamedListCons(struct BSQON_TYPE_AST_NamedListEntry* value, struct BSQON_TYPE_AST_NamedList* next);
struct BSQON_TYPE_AST_NamedList* BSQON_TYPE_AST_NamedListCompleteParse(struct BSQON_TYPE_AST_NamedList* ll);

enum BSQON_TYPE_AST_TAG BSQON_TYPE_AST_getTag(const struct BSQON_TYPE_AST_Node* node);
void BSQON_TYPE_AST_print(struct BSQON_TYPE_AST_Node* node);

struct BSQON_TYPE_AST_Node* BSQON_TYPE_AST_ErrorNodeCreate();

struct BSQON_TYPE_AST_NominalNode* BSQON_AST_asNominalNode(const struct BSQON_TYPE_AST_Node* node);
struct BSQON_TYPE_AST_Node* BSQON_AST_NominalNodeCreate(const char* name, struct BSQON_TYPE_AST_List* terms);
void BSQON_AST_TYPE_printNominalNode(struct BSQON_TYPE_AST_NominalNode* node);

struct BSQON_TYPE_AST_NominalExtNode* BSQON_AST_asNominalExtNode(const struct BSQON_TYPE_AST_Node* node);
struct BSQON_TYPE_AST_Node* BSQON_AST_NominalExtNodeCreate(struct BSQON_TYPE_AST_NominalNode* base, const char* ext);
void BSQON_AST_TYPE_printNominalExtNode(struct BSQON_TYPE_AST_NominalExtNode* node);

struct BSQON_TYPE_AST_TupleNode* BSQON_AST_asTupleNode(const struct BSQON_TYPE_AST_Node* node);
struct BSQON_TYPE_AST_Node* BSQON_AST_TupleNodeCreate(struct BSQON_TYPE_AST_List* types);
void BSQON_AST_TYPE_printTupleNode(struct BSQON_TYPE_AST_TupleNode* node);

struct BSQON_TYPE_AST_RecordNode* BSQON_AST_asRecordNode(const struct BSQON_TYPE_AST_Node* node);
struct BSQON_TYPE_AST_Node* BSQON_AST_RecordNodeCreate(struct BSQON_TYPE_AST_NamedList* entries);
void BSQON_AST_TYPE_printRecordNode(struct BSQON_TYPE_AST_RecordNode* node);

struct BSQON_TYPE_AST_Conjunction* BSQON_AST_asConjunction(const struct BSQON_TYPE_AST_Node* node);
struct BSQON_TYPE_AST_Node* BSQON_AST_ConjunctionCreate(struct BSQON_TYPE_AST_Node* left, struct BSQON_TYPE_AST_Node* right);
void BSQON_AST_TYPE_printConjunction(struct BSQON_TYPE_AST_Conjunction* node);

struct BSQON_TYPE_AST_Union* BSQON_AST_asUnion(const struct BSQON_TYPE_AST_Node* node);
struct BSQON_TYPE_AST_Node* BSQON_AST_UnionCreate(struct BSQON_TYPE_AST_Node* left, struct BSQON_TYPE_AST_Node* right);
void BSQON_AST_TYPE_printUnion(struct BSQON_TYPE_AST_Union* node);

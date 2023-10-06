#include "./bsqon_type_ast.h"

#include <stdio.h>

#include <assert.h>

struct BSQON_TYPE_AST_List* BSQON_TYPE_AST_ListCons(struct BSQON_TYPE_AST_Node* value, struct BSQON_TYPE_AST_List* next)
{
    struct BSQON_TYPE_AST_List* node = (struct BSQON_TYPE_AST_List*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_List));
    node->value = value;
    node->next = next;
}

struct BSQON_TYPE_AST_List* BSQON_TYPE_AST_ListCompleteParse(struct BSQON_TYPE_AST_List* ll)
{
    assert(false);
}

struct BSQON_TYPE_AST_List* BSQON_TYPE_AST_NamedListCons(struct ByteString name, struct BSQON_TYPE_AST_Node* value, struct BSQON_TYPE_AST_List* next)
{
    assert(false);
}

struct BSQON_TYPE_AST_NamedList* BSQON_TYPE_AST_NamedListCompleteParse(struct BSQON_TYPE_AST_NamedList* ll)
{
    assert(false);
}

enum BSQON_TYPE_AST_TAG BSQON_TYPE_AST_getTag(const struct BSQON_TYPE_AST_Node* node)
{
    return node->tag;
}

void BSQON_TYPE_AST_delete(struct BSQON_TYPE_AST_Node* node)
{
    assert(false);
}

void BSQON_TYPE_AST_print(struct BSQON_TYPE_AST_Node* node)
{
    assert(false);
}

struct BSQON_TYPE_AST_NominalNode* BSQON_AST_asNominalNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_NominalNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_NominalNodeCreate(const char* name, struct BSQON_TYPE_AST_List* terms)
{
    assert(false);
    return NULL;
}

void BSQON_AST_TYPE_printNominalNode(struct BSQON_TYPE_AST_NominalNode* node)
{
    assert(false);
}

struct BSQON_TYPE_AST_TupleNode* BSQON_AST_asTupleNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_TupleNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_TupleNodeCreate(struct BSQON_TYPE_AST_List* types)
{
    assert(false);
    return NULL;
}

void BSQON_AST_TYPE_printTupleNode(struct BSQON_TYPE_AST_TupleNode* node)
{
    assert(false);
}

struct BSQON_TYPE_AST_RecordNode* BSQON_AST_asRecordNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_RecordNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_RecordNodeCreate(struct BSQON_TYPE_AST_NamedList* entries)
{
    assert(false);
    return NULL;
}

void BSQON_AST_TYPE_printRecordNode(struct BSQON_TYPE_AST_RecordNode* node)
{
    assert(false);
}

struct BSQON_TYPE_AST_Conjunction* BSQON_AST_asConjunction(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_Conjunction*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_ConjunctionCreate(struct BSQON_TYPE_AST_List* opts)
{
    assert(false);
    return NULL;
}

void BSQON_AST_TYPE_printConjunction(struct BSQON_TYPE_AST_Conjunction* node)
{
    assert(false);
}

struct BSQON_TYPE_AST_Union* BSQON_AST_asUnion(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_Union*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_UnionCreate(struct BSQON_TYPE_AST_List* opts)
{
    assert(false);
    return NULL;
}

void BSQON_AST_TYPE_printUnion(struct BSQON_TYPE_AST_Union* node)
{
    assert(false);
}

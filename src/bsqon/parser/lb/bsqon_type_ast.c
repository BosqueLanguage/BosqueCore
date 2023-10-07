#include "./bsqon_type_ast.h"

#include <stdio.h>

#include <assert.h>

struct BSQON_TYPE_AST_List* BSQON_TYPE_AST_ListCons(struct BSQON_TYPE_AST_Node* value, struct BSQON_TYPE_AST_List* next)
{
    struct BSQON_TYPE_AST_List* node = (struct BSQON_TYPE_AST_List*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_List));
    node->value = value;
    node->next = next;

    return node;
}

struct BSQON_TYPE_AST_List* BSQON_TYPE_AST_ListCompleteParse(struct BSQON_TYPE_AST_List* ll)
{
    assert(ll != NULL);

    struct BSQON_TYPE_AST_List* lp = NULL;
    while(ll != NULL) {
        struct BSQON_TYPE_AST_List* lc = ll;
        ll = ll->next;

        lc->next = lp;
        lp = lc;
    }

    return lp;
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

void BSQON_TYPE_AST_print(struct BSQON_TYPE_AST_Node* node)
{
    switch (node->tag)
    {
    case BSQON_TYPE_AST_TAG_Error: {
        printf("^ERROR_TYPE^");
        break;
    }
    case BSQON_TYPE_AST_TAG_Nominal: {
        BSQON_AST_TYPE_printNominalNode(BSQON_AST_asNominalNode(node));
        break;
    }
    default: {
        printf("unknown");
        assert(false);
    }
    }
}

struct BSQON_TYPE_AST_Node* BSQON_AST_ErrorNodeCreate()
{
    struct BSQON_TYPE_AST_ErrorNode* node = (struct BSQON_TYPE_AST_ErrorNode*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_ErrorNode));
    node->base.tag = BSQON_TYPE_AST_TAG_Error;

    return (struct BSQON_TYPE_AST_Node*)node;
}

struct BSQON_TYPE_AST_NominalNode* BSQON_AST_asNominalNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_NominalNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_NominalNodeCreate(const char* name, struct BSQON_TYPE_AST_List* terms)
{
    size_t length = strlen(name);

    struct BSQON_TYPE_AST_NominalNode* node = (struct BSQON_TYPE_AST_NominalNode*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_NominalNode) + length + 1);
    node->base.tag = BSQON_TYPE_AST_TAG_Nominal;
    node->name.bytes = ((uint8_t*)node) + sizeof(struct BSQON_TYPE_AST_NominalNode);
    node->terms = terms;

    buff_clear(node->name.bytes, length + 1);
    chars_copy(&(node->name), name, length);

    return (struct BSQON_TYPE_AST_Node*)node;
}

void BSQON_AST_TYPE_printNominalNode(struct BSQON_TYPE_AST_NominalNode* node)
{
    printf("%s", node->name.bytes);
    if(node->terms != NULL) {
        printf("<");
        for(struct BSQON_TYPE_AST_List* ll = node->terms; ll != NULL; ll = ll->next)
        {
            BSQON_TYPE_AST_print(ll->value);
            if(ll->next != NULL) {
                printf(", ");
            }
        }
        printf(">");
    }
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

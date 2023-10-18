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

struct BSQON_TYPE_AST_NamedListEntry* BSQON_TYPE_AST_NamedListEntryCreate(const char* name, struct BSQON_TYPE_AST_Node* value)
{
    struct BSQON_TYPE_AST_NamedListEntry* node = (struct BSQON_TYPE_AST_NamedListEntry*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_NamedListEntry));
    node->name = name;
    node->value = value;

    return (struct BSQON_TYPE_AST_NamedListEntry*)node;
}

struct BSQON_TYPE_AST_NamedList* BSQON_TYPE_AST_NamedListCons(struct BSQON_TYPE_AST_NamedListEntry* value, struct BSQON_TYPE_AST_NamedList* next)
{
    struct BSQON_TYPE_AST_NamedList* node = (struct BSQON_TYPE_AST_NamedList*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_NamedList));
    node->value = value;
    node->next = next;

    return node;
}

struct BSQON_TYPE_AST_NamedList* BSQON_TYPE_AST_NamedListCompleteParse(struct BSQON_TYPE_AST_NamedList* ll)
{
    assert(ll != NULL);

    struct BSQON_TYPE_AST_NamedList* lp = NULL;
    while(ll != NULL) {
        struct BSQON_TYPE_AST_NamedList* lc = ll;
        ll = ll->next;

        lc->next = lp;
        lp = lc;
    }

    return lp;
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
    case BSQON_TYPE_AST_TAG_Tuple: {
        BSQON_AST_TYPE_printTupleNode(BSQON_AST_asTupleNode(node));
        break;
    }
    case BSQON_TYPE_AST_TAG_Record: {
        BSQON_AST_TYPE_printRecordNode(BSQON_AST_asRecordNode(node));
        break;
    }
    case BSQON_TYPE_AST_TAG_Conjunction: {
        BSQON_AST_TYPE_printConjunction(BSQON_AST_asConjunction(node));
        break;
    }
    case BSQON_TYPE_AST_TAG_Union: {
        BSQON_AST_TYPE_printUnion(BSQON_AST_asUnion(node));
        break;
    }
    default: {
        printf("unknown");
        assert(false);
    }
    }
}

struct BSQON_TYPE_AST_Node* BSQON_TYPE_AST_ErrorNodeCreate(struct SourcePos pos)
{
    struct BSQON_TYPE_AST_ErrorNode* node = (struct BSQON_TYPE_AST_ErrorNode*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_ErrorNode));
    node->base.tag = BSQON_TYPE_AST_TAG_Error;
    node->base.pos = pos;

    return (struct BSQON_TYPE_AST_Node*)node;
}

struct BSQON_TYPE_AST_NominalNode* BSQON_AST_asNominalNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_NominalNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_NominalNodeCreate(const char* name, struct BSQON_TYPE_AST_List* terms)
{
    struct BSQON_TYPE_AST_NominalNode* node = (struct BSQON_TYPE_AST_NominalNode*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_NominalNode));
    node->base.tag = BSQON_TYPE_AST_TAG_Nominal;
    node->name = name;
    node->terms = terms;

    return (struct BSQON_TYPE_AST_Node*)node;
}

void BSQON_AST_TYPE_printNominalNode(struct BSQON_TYPE_AST_NominalNode* node)
{
    printf("%s", node->name);
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

struct BSQON_TYPE_AST_NominalExtNode* BSQON_AST_asNominalExtNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_NominalExtNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_NominalExtNodeCreate(struct BSQON_TYPE_AST_NominalNode* base, const char* ext)
{
    assert(false);
}

void BSQON_AST_TYPE_printNominalExtNode(struct BSQON_TYPE_AST_NominalExtNode* node)
{
    BSQON_AST_TYPE_printNominalNode(node->root);
    printf("::%s", node->ext.bytes);
}

struct BSQON_TYPE_AST_TupleNode* BSQON_AST_asTupleNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_TupleNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_TupleNodeCreate(struct BSQON_TYPE_AST_List* types)
{
    struct BSQON_TYPE_AST_TupleNode* node = (struct BSQON_TYPE_AST_TupleNode*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_TupleNode));
    node->base.tag = BSQON_TYPE_AST_TAG_Tuple;
    node->types = types;

    return (struct BSQON_TYPE_AST_Node*)node;
}

void BSQON_AST_TYPE_printTupleNode(struct BSQON_TYPE_AST_TupleNode* node)
{
    printf("[");
    for(struct BSQON_TYPE_AST_List* ll = node->types; ll != NULL; ll = ll->next) {
        BSQON_TYPE_AST_print(ll->value);

        if(ll->next != NULL) {
            printf(", ");
        }
    }
    printf("]");
}

struct BSQON_TYPE_AST_RecordNode* BSQON_AST_asRecordNode(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_RecordNode*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_RecordNodeCreate(struct BSQON_TYPE_AST_NamedList* entries)
{
    struct BSQON_TYPE_AST_RecordNode* node = (struct BSQON_TYPE_AST_RecordNode*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_RecordNode));
    node->base.tag = BSQON_TYPE_AST_TAG_Record;
    node->entries = entries;

    return (struct BSQON_TYPE_AST_Node*)node;
}

void BSQON_AST_TYPE_printRecordNode(struct BSQON_TYPE_AST_RecordNode* node)
{
    printf("{");
    for(struct BSQON_TYPE_AST_NamedList* ll = node->entries; ll != NULL; ll = ll->next) {
        printf("%s: ", ll->value->name);
        BSQON_TYPE_AST_print(ll->value->value);

        if(ll->next != NULL) {
            printf(", ");
        }
    }
    printf("}");
}

struct BSQON_TYPE_AST_Conjunction* BSQON_AST_asConjunction(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_Conjunction*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_ConjunctionCreate(struct BSQON_TYPE_AST_Node* left, struct BSQON_TYPE_AST_Node* right)
{
    struct BSQON_TYPE_AST_Conjunction* node = (struct BSQON_TYPE_AST_Conjunction*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_Conjunction));
    node->base.tag = BSQON_TYPE_AST_TAG_Conjunction;
    node->left = left;
    node->right = right;

    return (struct BSQON_TYPE_AST_Node*)node;
}

void BSQON_AST_TYPE_printConjunction(struct BSQON_TYPE_AST_Conjunction* node)
{
    BSQON_TYPE_AST_print(node->left);
    printf(" & ");
    BSQON_TYPE_AST_print(node->right);
}

struct BSQON_TYPE_AST_Union* BSQON_AST_asUnion(const struct BSQON_TYPE_AST_Node* node)
{
    return (struct BSQON_TYPE_AST_Union*)node;
}

struct BSQON_TYPE_AST_Node* BSQON_AST_UnionCreate(struct BSQON_TYPE_AST_Node* left, struct BSQON_TYPE_AST_Node* right)
{
    struct BSQON_TYPE_AST_Union* node = (struct BSQON_TYPE_AST_Union*)AST_ALLOC(sizeof(struct BSQON_TYPE_AST_Union));
    node->base.tag = BSQON_TYPE_AST_TAG_Union;
    node->left = left;
    node->right = right;

    return (struct BSQON_TYPE_AST_Node*)node;
}

void BSQON_AST_TYPE_printUnion(struct BSQON_TYPE_AST_Union* node)
{
    
    if(BSQON_TYPE_AST_getTag(node->left) != BSQON_TYPE_AST_TAG_Conjunction) {
        BSQON_TYPE_AST_print(node->left);
    }
    else {
        printf("(");
        BSQON_TYPE_AST_print(node->left);
        printf(")");
    }
        
    printf(" | ");

    if(BSQON_TYPE_AST_getTag(node->right) != BSQON_TYPE_AST_TAG_Conjunction) {
        BSQON_TYPE_AST_print(node->right);
    }
    else {
        printf("(");
        BSQON_TYPE_AST_print(node->right);
        printf(")");
    }
}

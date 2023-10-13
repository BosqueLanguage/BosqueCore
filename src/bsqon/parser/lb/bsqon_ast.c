#include "./bsqon_ast.h"

#include <stdio.h>

struct BSQON_AST_List* BSQON_AST_ListCons(struct BSQON_AST_Node* value, struct BSQON_AST_List* next)
{
    struct BSQON_AST_List* node = (struct BSQON_AST_List*)AST_ALLOC(sizeof(struct BSQON_AST_List));
    node->value = value;
    node->next = next;

    return node;
}

struct BSQON_AST_List* BSQON_AST_ListCompleteParse(struct BSQON_AST_List* ll)
{
    assert(ll != NULL);

    struct BSQON_AST_List* lp = NULL;
    while(ll != NULL) {
        struct BSQON_AST_List* lc = ll;
        ll = ll->next;

        lc->next = lp;
        lp = lc;
    }

    return lp;
}

struct BSQON_AST_NamedListEntry* BSQON_AST_NamedListEntryCreate(const char* name, struct BSQON_AST_Node* value)
{
    xxxx;
}

struct BSQON_AST_NamedList* BSQON_AST_NamedListCons(struct BSQON_AST_NamedListEntry* value, struct BSQON_TYPE_AST_NamedList* next)
{
    xxxx;
}

struct BSQON_AST_NamedList* BSQON_AST_NamedListCompleteParse(struct BSQON_AST_NamedList* ll)
{
    xxxx;
}

enum BSQON_AST_TAG BSQON_AST_getTag(const struct BSQON_AST_Node* node)
{
    return node->tag;
}

void BSQON_AST_print(struct BSQON_AST_Node* node)
{
    switch (node->tag)
    {
    case BSQON_AST_TAG_Error:
        printf("^ERROR_EXP^");
        break;
    case BSQON_AST_TAG_None:
        printf("none");
        break;
    case BSQON_AST_TAG_Nothing:
        printf("nothing");
        break;
    case BSQON_AST_TAG_True:
        printf("true");
        break;
    case BSQON_AST_TAG_False:
        printf("false");
        break;
    case BSQON_AST_TAG_String:
    case BSQON_AST_TAG_ASCIIString:
    case BSQON_AST_TAG_Regex:
        BSQON_AST_LiteralStringNode_print(BSQON_AST_asLiteralStringNode(node));
        break;
    case BSQON_AST_TAG_Identifier:
    case BSQON_AST_TAG_UnspecIdentifier:
        BSQON_AST_NameNode_print(BSQON_AST_asNameNode(node));
        break;
    case BSQON_AST_TAG_StringOf:
    case BSQON_AST_TAG_ASCIIStringOf:
        BSQON_AST_StringOfNode_print(BSQON_AST_asStringOfNode(node));
        break;
    case BSQON_AST_TAG_Path:
        BSQON_AST_PathNode_print(BSQON_AST_asPathNode(node));
        break;
    case BSQON_AST_TAG_TypedLiteral:
        BSQON_AST_TypedLiteralNode_print(BSQON_AST_asTypedLiteralNode(node));
        break;
    default:
        BSQON_AST_LiteralStandardNode_print(BSQON_AST_asLiteralStandardNode(node));
        break;
    }
}

struct BSQON_AST_Node* BSQON_AST_ErrorNodeCreate()
{
    struct BSQON_AST_ErrorNode* node = (struct BSQON_AST_ErrorNode*)AST_ALLOC(sizeof(struct BSQON_AST_ErrorNode));
    node->base.tag = BSQON_AST_TAG_Error;

    return (struct BSQON_AST_Node*)node;
}

struct BSQON_AST_LiteralSingletonNode* BSQON_AST_asLiteralSingletonNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_LiteralSingletonNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_LiteralSingletonNodeCreate(enum BSQON_AST_TAG tag)
{
    struct BSQON_AST_LiteralSingletonNode* node = (struct BSQON_AST_LiteralSingletonNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralSingletonNode));
    node->base.tag = tag;

    return (struct BSQON_AST_Node*)node;
}

struct BSQON_AST_LiteralStringNode* BSQON_AST_asLiteralStringNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_LiteralStringNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_LiteralStringNodeCreate(enum BSQON_AST_TAG tag, struct ByteString* data)
{
    struct BSQON_AST_LiteralStringNode* node = (struct BSQON_AST_LiteralStringNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralStringNode));
    node->base.tag = tag;
    node->data = data;

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_LiteralStringNode_print(struct BSQON_AST_LiteralStringNode* node)
{
    printf("%s", node->data->bytes);
}

struct BSQON_AST_LiteralStandardNode* BSQON_AST_asLiteralStandardNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_LiteralStandardNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_LiteralStandardNodeCreate(enum BSQON_AST_TAG tag, const char* data)
{
    struct BSQON_AST_LiteralStandardNode* node = (struct BSQON_AST_LiteralStandardNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralStandardNode));
    node->base.tag = tag;
    node->data = data;

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_LiteralStandardNode_print(struct BSQON_AST_LiteralStandardNode* node)
{
    printf("%s", node->data);
}

struct BSQON_AST_NameNode* BSQON_AST_asNameNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_NameNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_NameNodeCreate(enum BSQON_AST_TAG tag, const char* data)
{
    struct BSQON_AST_NameNode* node = (struct BSQON_AST_NameNode*)AST_ALLOC(sizeof(struct BSQON_AST_NameNode));
    node->base.tag = tag;
    node->data = data;

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_NameNode_print(struct BSQON_AST_NameNode* node)
{
    printf("%s", node->data);
}

struct BSQON_AST_StringOfNode* BSQON_AST_asStringOfNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_StringOfNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_StringOfNodeCreate(enum BSQON_AST_TAG tag, struct ByteString* str, struct BSQON_TYPE_AST_Node* type)
{
    struct BSQON_AST_StringOfNode* node = (struct BSQON_AST_StringOfNode*)AST_ALLOC(sizeof(struct BSQON_AST_StringOfNode));
    node->base.tag = tag;
    node->data = str;
    node->type = type;

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_StringOfNode_print(struct BSQON_AST_StringOfNode* node)
{
    printf("%s", node->data->bytes);
    BSQON_TYPE_AST_print(node->type);
}

struct BSQON_AST_PathNode* BSQON_AST_asPathNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_PathNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_PathNodeCreate(struct ByteString* str, struct BSQON_TYPE_AST_Node* type)
{
    struct BSQON_AST_PathNode* node = (struct BSQON_AST_PathNode*)AST_ALLOC(sizeof(struct BSQON_AST_PathNode));
    node->base.tag = BSQON_AST_TAG_Path;
    node->data = str;
    node->type = type;

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_PathNode_print(struct BSQON_AST_PathNode* node)
{
    printf("%s", node->data->bytes);
    BSQON_TYPE_AST_print(node->type);
}

struct BSQON_AST_TypedLiteralNode* BSQON_AST_asTypedLiteralNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_TypedLiteralNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_TypedLiteralNodeCreate(struct BSQON_AST_Node* data, struct BSQON_TYPE_AST_Node* type)
{
    struct BSQON_AST_TypedLiteralNode* node = (struct BSQON_AST_TypedLiteralNode*)AST_ALLOC(sizeof(struct BSQON_AST_TypedLiteralNode));
    node->base.tag = BSQON_AST_TAG_TypedLiteral;
    node->data = data;
    node->type = type;

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_TypedLiteralNode_print(struct BSQON_AST_TypedLiteralNode* node)
{
    BSQON_AST_print((struct BSQON_AST_Node*)node->data);
    printf("_");
    BSQON_TYPE_AST_print(node->type);
}

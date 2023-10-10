#include "./bsqon_ast.h"

#include <stdio.h>

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
    case BSQON_AST_TAG_Identifier:
    case BSQON_AST_TAG_UnspecIdentifier:
        BSQON_AST_NameNode_print(BSQON_AST_asNameNode(node));
        break;
    case BSQON_AST_TAG_TypedLiteral:
        BSQON_AST_TypedLiteralNode_print(BSQON_AST_asTypedLiteralNode(node));
        break;
    default:
        BSQON_AST_LiteralNode_print(BSQON_AST_asLiteralNode(node));
        break;
    }
}

struct BSQON_AST_Node* BSQON_AST_ErrorNodeCreate()
{
    struct BSQON_AST_ErrorNode* node = (struct BSQON_AST_ErrorNode*)AST_ALLOC(sizeof(struct BSQON_AST_ErrorNode));
    node->base.tag = BSQON_AST_TAG_Error;

    return (struct BSQON_AST_Node*)node;
}

struct BSQON_AST_LiteralNode* BSQON_AST_asLiteralNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_LiteralNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_LiteralNodeCreateEmpty(enum BSQON_AST_TAG tag)
{
    struct BSQON_AST_LiteralNode* node = (struct BSQON_AST_LiteralNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralNode));
    node->base.tag = tag;
    node->data.bytes = NULL;
    node->data.len = 0;

    return (struct BSQON_AST_Node*)node;
}

struct BSQON_AST_Node* BSQON_AST_LiteralNodeCreateChars(enum BSQON_AST_TAG tag, const char* data)
{
    size_t length = strlen(data);

    struct BSQON_AST_LiteralNode* node = (struct BSQON_AST_LiteralNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralNode) + length + 1);
    node->base.tag = tag;
    node->data.bytes = ((uint8_t*)node) + sizeof(struct BSQON_AST_LiteralNode);

    buff_clear(node->data.bytes, length + 1);
    chars_copy(&(node->data), data, length);

    return (struct BSQON_AST_Node*)node;
}

struct BSQON_AST_Node* BSQON_AST_LiteralNodeCreateBytes(enum BSQON_AST_TAG tag, struct ByteString* data)
{
    struct BSQON_AST_LiteralNode* node = (struct BSQON_AST_LiteralNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralNode) + data->len + 1);
    node->base.tag = tag;
    node->data.bytes = ((uint8_t*)node) + sizeof(struct BSQON_AST_LiteralNode);

    buff_clear(node->data.bytes, data->len + 1);
    bytes_copy(&(node->data), data);

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_LiteralNode_print(struct BSQON_AST_LiteralNode* node)
{
   printf("%s", node->data.bytes);
}

struct BSQON_AST_NameNode* BSQON_AST_asNameNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_NameNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_NameNodeCreate(enum BSQON_AST_TAG tag, const char* data)
{
    size_t length = strlen(data);

    struct BSQON_AST_NameNode* node = (struct BSQON_AST_NameNode*)AST_ALLOC(sizeof(struct BSQON_AST_NameNode) + length + 1);
    node->base.tag = tag;
    node->data.bytes = ((uint8_t*)node) + sizeof(struct BSQON_AST_NameNode);

    buff_clear(node->data.bytes, length + 1);
    chars_copy(&(node->data), data, length);

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_NameNode_print(struct BSQON_AST_NameNode* node)
{
    printf("%s", node->data.bytes);
}

struct BSQON_AST_TypedLiteralNode* BSQON_AST_asTypedLiteralNode(const struct BSQON_AST_Node* node)
{
    return (struct BSQON_AST_TypedLiteralNode*)node;
}

struct BSQON_AST_Node* BSQON_AST_TypedLiteralNodeCreate(struct BSQON_AST_LiteralNode* data, struct BSQON_TYPE_AST_Node* type)
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

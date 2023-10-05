#include "./bsqon_ast.h"

#include <stdio.h>

#define AST_ALLOC_ALIGN_8(size) (((size) + 7) & ~7)
#define AST_ALLOC(size) malloc(AST_ALLOC_ALIGN_8(size))
#define AST_FREE(ptr) free(ptr)

void buff_clear(char* src, size_t len)
{
    memset(src, 0, len);
}

void chars_copy(struct ByteString* dst, const char* src, size_t len)
{
    memcpy(dst->bytes, src, len);
    dst->len = len;
}

void bytes_copy(struct ByteString* dst, struct ByteString* src)
{
    memcpy(dst->bytes, src->bytes, src->len);
    dst->len = src->len;
}

enum BSQON_AST_TAG getTag(const struct BSQON_AST_Node* node)
{
    return node->tag;
}

void BSQON_AST_delete(struct BSQON_AST_Node* node)
{
    AST_FREE(node);
}

void BSQON_AST_print(struct BSQON_AST_Node* node)
{
    switch (node->tag)
    {
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
    default:
        BSQON_AST_LiteralNode_print(BSQON_AST_asLiteralNode(node));
        break;
    }
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

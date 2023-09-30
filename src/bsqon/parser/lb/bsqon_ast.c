#include "./bsqon_ast.h"

#include <stdio.h>

#define AST_ALLOC_ALIGN_8(size) (((size) + 7) & ~7)
#define AST_ALLOC(size) malloc(AST_ALLOC_ALIGN_8(size))
#define AST_FREE(ptr) free(ptr)

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
    case BSQON_AST_TAG_Null:
        printf("null");
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

    struct BSQON_AST_LiteralNode* node = (struct BSQON_AST_LiteralNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralNode) + length);
    node->base.tag = tag;
    node->data.bytes = ((uint8_t*)data) + sizeof(struct BSQON_AST_LiteralNode);
    chars_copy(&(node->data), data, length);

    return (struct BSQON_AST_Node*)node;
}

struct BSQON_AST_Node* BSQON_AST_LiteralNodeCreateBytes(enum BSQON_AST_TAG tag, struct ByteString* data)
{
    struct BSQON_AST_LiteralNode* node = (struct BSQON_AST_LiteralNode*)AST_ALLOC(sizeof(struct BSQON_AST_LiteralNode) + data->len);
    node->base.tag = tag;
    node->data.bytes = ((uint8_t*)data) + sizeof(struct BSQON_AST_LiteralNode);
    bytes_copy(&(node->data), data);

    return (struct BSQON_AST_Node*)node;
}

void BSQON_AST_LiteralNode_print(struct BSQON_AST_LiteralNode* node)
{
    for(uint64_t i = 0; i < node->data.len; ++i)
    {
        uint8_t c = node->data.bytes[i];
        if((uint8_t)32 <= c && c <= (uint8_t)126) {
            printf("%c", node->data.bytes[i]);
        }
        else {
            printf("[\\u%hhu]", (unsigned char)node->data.bytes[i]);
        }
    }
}

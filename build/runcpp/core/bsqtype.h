#pragma once

#include "../common.h"

#include "../runtime/utils/lexer.h"
#include "../runtime/utils/builder.h"
#include "../runtime/utils/encodings.h"

#define BSQ_PTR_MASK_LEAF nullptr

namespace ᐸRuntimeᐳ
{
    //forward declare
    class TypeInfo;

    enum class RColor : uint16_t
    {
        Red,
        Black
    };
    
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_NONE = 0;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BOOL = 1;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_INT = 2;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_NAT = 3;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CHKINT = 4;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CHKNAT = 5;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_FLOAT = 6;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_CSTRING = 7;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_CSTRING = 8;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING = 9;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING_INLINE = 10;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING_TREE = 11;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING = 12;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_STRING = 13;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_STRING = 14;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING = 15;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING_INLINE = 16;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING_TREE = 17;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING = 18;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY = 19;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERBLOCK = 20;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFER = 21;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTE = 22;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CCHAR = 23;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_UNICODECHAR = 24;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_UUIDV4 = 25;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_UUIDV7 = 26;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CREGEX = 27;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_REGEX = 28;

    enum class LayoutTag : uint16_t
    {
        Value,     //an inline value
        Ref        //a pointer to a heap allocated value
    };

    //Function pointer type for entrypoint constructors will run all needed validations on arguments (passed as pointer array of void* and write the constructed value to the second void* argument) -- this needs to handle long jump on error
    using ValidatingConstructorFp = void(*)(void**, void*); 

    //Function pointer type for JSON to BSQ conversion (takes the target typeinfo, a JSON object, and a pointer to the destination BSQ value) -- this needs to handle long jump on error
    using JSONParseToBSQFp = void(*)(const TypeInfo*, const json&, void*);

    //Function pointer type for parser to BSQ conversion (takes the target typeinfo, a parser object, and a pointer to the destination BSQ value) -- this needs to handle long jump on error
    using ParseToBSQFp = void(*)(const TypeInfo*, BAPILexer*, void*);

    //Function pointer type to convert a BSQ value to JSON (takes the source typeinfo, a pointer to the source BSQ value, and a JSON object to write to)
    using BSQToJSONFp = json(*)(const TypeInfo*, const void*);

    //Function pointer type to convert a BSQ value to BAPI (takes the source typeinfo, a pointer to the source BSQ value, and a out buffer (iobuffer or ByteBuffer writer) to write to)
    using BSQToBAPIFp = void(*)(const TypeInfo*, const void*, BSQStreamingBuilder*); 

    //Function pointer to write a value for display (diagnostics)
    using DisplayValueFp = void(*)(const TypeInfo*, const void*, std::ostream&, std::optional<std::string>); 

    class TypeOpDispatchInfo
    {
    public:
        ValidatingConstructorFp validatingConstructorFp;
        JSONParseToBSQFp jsonParseToBSQFp;
        ParseToBSQFp parseToBSQFp;
        BSQToJSONFp bsqToJSONFp;
        BSQToBAPIFp bsqToBAPIFp;
        DisplayValueFp displayFp;

        constexpr TypeOpDispatchInfo() : validatingConstructorFp{}, jsonParseToBSQFp{}, parseToBSQFp{}, bsqToJSONFp{}, bsqToBAPIFp{}, displayFp{} {}
        constexpr TypeOpDispatchInfo(ValidatingConstructorFp validatingConstructorFp, JSONParseToBSQFp jsonParseToBSQFp, ParseToBSQFp parseToBSQFp, BSQToJSONFp bsqToJSONFp, BSQToBAPIFp bsqToBAPIFp, DisplayValueFp displayFp) : validatingConstructorFp(validatingConstructorFp), jsonParseToBSQFp(jsonParseToBSQFp), parseToBSQFp(parseToBSQFp), bsqToJSONFp(bsqToJSONFp), bsqToBAPIFp(bsqToBAPIFp), displayFp(displayFp) {}
    };

    class TypeLayoutInfo
    {
    public:
        int32_t fieldid;
        uint32_t fieldbsqtypeid;
        uint32_t byteoffset;
        uint32_t slotoffset;

        const char* fieldkey;
        const char* fname;
    };

    using VInvokePtr = void(*)(void);
    class VInvokeTargetInfo
    {
    public:
        uint32_t invokeid;
        VInvokePtr invokeptr;

        const char* invokekey;
    };

    class TypeInfo
    {
    public:
        uint32_t bsqtypeid;
        uint32_t bytesize;
        uint32_t slotcount;
        LayoutTag tag;
        
        const char* ptrmask; // NULL is for leaf values or structs

        const uint32_t* supertypes;
        const uint32_t supertypescount;
        const TypeLayoutInfo* ftable;
        const uint32_t ftablecount;
        const VInvokeTargetInfo* vitable;
        const uint32_t vitablecount;
        const TypeOpDispatchInfo opdispatch;

        const char* typekey;

        bool quickrelease;

        //Way to get any typeinfo by its bsqtypeid -- map might be slower than desired (and not static initializable -- maybe evaluate later)
        static std::unordered_map<std::string, uint32_t> tkeytoidmap;
        static std::unordered_map<uint32_t, const TypeInfo*> tinfomap;

        //For enum types, this map provides quick access to enum names
        static std::unordered_map<uint32_t, std::pair<size_t, const char**>> enuminfomap;

        inline static std::optional<const TypeInfo*> tryGetTypeInfoForKey(const std::string& key)
        {
            auto ii = tkeytoidmap.find(key);
            return (ii != tkeytoidmap.end()) ? std::optional<const TypeInfo*>(tinfomap.at(ii->second)) : std::nullopt;
        }

        inline static const TypeInfo* getTypeInfoForKey(const std::string& key)
        {
            return tinfomap.at(tkeytoidmap.at(key));
        }

        inline static const TypeInfo* getTypeInfoForID(uint32_t id)
        {
            return tinfomap.at(id);
        }
    };

    consteval uint32_t byteSizeToSlotCount(size_t bytesize)
    {
        return bytesize / sizeof(uint64_t);
    }

    consteval uint32_t slotCountToByteSize(size_t slotcount)
    {
        return slotcount * sizeof(uint64_t);
    }

    ////////////////////////////////
    //Standard processing functions for Enum types
    ////////////////////////////////
    void jsonParseToBSQ_Enum(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_Enum(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_Enum(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_Enum(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_Enum(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    ////////////////////////////////
    //Standard processing functions for Typedecl types
    ////////////////////////////////
    void jsonParseToBSQ_Typedecl(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_Typedecl(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_Typedecl(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_Typedecl(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_Typedecl(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    ////////////////////////////////
    //Standard processing functions for Entity types
    ////////////////////////////////
    void jsonParseToBSQ_Entity(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_Entity(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_Entity(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_Entity(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_Entity(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);
}

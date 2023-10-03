
#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"

namespace BSQON
{
    //
    //TODO: this is not very performant (easy to debug though) we should do a numeric ID map or intern to string pointers later
    //
    using TypeKey = std::string;

    enum class TypeTag
    {
        TYPE_UNRESOLVED = 0x0,
        TYPE_TUPLE,
        TYPE_RECORD,
        TYPE_STD_ENTITY,
        TYPE_STD_CONCEPT,
        TYPE_PRIMITIVE,
        TYPE_ENUM,
        TYPE_TYPE_DECL,
        TYPE_VALIDATOR_RE,
        TYPE_VALIDATOR_PTH,
        TYPE_STRING_OF,
        TYPE_ASCII_STRING_OF,
        TYPE_SOMETHING,
        TYPE_OPTION,
        TYPE_OK,
        TYPE_ERROR,
        TYPE_RESULT,
        TYPE_PATH,
        TYPE_PATH_FRAGMENT,
        TYPE_PATH_GLOB,
        TYPE_LIST,
        TYPE_STACK,
        TYPE_QUEUE,
        TYPE_SET,
        TYPE_MAP_ENTRY,
        TYPE_MAP,
        TYPE_CONCEPT_SET,
        TYPE_UNION
    };

    class Type
    {
    public:
        TypeTag tag;
        TypeKey tkey;

        Type(TypeTag tag, TypeKey tkey) : tag(tag), tkey(tkey)
        {
            ;
        }

        virtual ~Type()
        {
            ;
        }

        static const int64_t MIN_SAFE_NUMBER = -9007199254740991;
        static const int64_t MAX_SAFE_NUMBER = 9007199254740991;

        virtual const std::vector<TypeKey>* getPossibleSubtypeKeys() const
        {
            return nullptr;
        }

        static Type* parse(json j);

        inline bool isUnresolved() const
        {
            return this->tag == TypeTag::TYPE_UNRESOLVED;
        }
    };

    class UnresolvedType : public Type
    {
    public:
        UnresolvedType() : Type(TypeTag::TYPE_UNRESOLVED, "[UNRESOLVED]")
        {
            ;
        }

        virtual ~UnresolvedType()
        {
            ;
        }

        static UnresolvedType* singleton;
    };

    class TupleType : public Type
    {
    public:
        std::vector<TypeKey> entries;

        TupleType(std::vector<TypeKey> entries) : Type(TypeTag::TYPE_TUPLE, "[" + std::accumulate(entries.begin(), entries.end(), std::string(), [](std::string& a, TypeKey& b) { return a + ", " + b; }) + "]"), entries(entries)
        {
            ;
        }
        
        virtual ~TupleType()
        {
            ;
        }
    };

    class RecordTypeEntry
    {
    public:
        std::string pname;
        TypeKey ptype;

        RecordTypeEntry(std::string pname, TypeKey ptype) : pname(pname), ptype(ptype)
        {
            ;
        }
    };

    class RecordType : public Type
    {
    public:
        std::vector<RecordTypeEntry> entries;

        RecordType(std::vector<RecordTypeEntry> entries) : Type(TypeTag::TYPE_RECORD, "{" + std::accumulate(entries.begin(), entries.end(), std::string(), [](std::string& a, RecordTypeEntry& b) { return a + ", " + b.pname + ": " + b.ptype; }) + "}"), entries(entries)
        {
            ;
        }

        virtual ~RecordType()
        {
            ;
        }
    };

    class EntityType : public Type
    {
    public:
        EntityType(TypeTag tag, TypeKey tkey) : Type(tag, tkey)
        {
            ;
        }

        virtual ~EntityType()
        {
            ;
        }
    };

    class ConceptType : public Type
    {
    public:
        std::vector<TypeKey> subtypes;

        ConceptType(TypeTag tag, TypeKey tkey, std::vector<TypeKey> subtypes) : Type(tag, tkey), subtypes(subtypes)
        {
            std::sort(this->subtypes.begin(), this->subtypes.end());
        }

        virtual ~ConceptType()
        {
            ;
        }

        virtual const std::vector<TypeKey>* getPossibleSubtypeKeys() const override final
        {
            return &this->subtypes;
        }
    };

    class EntityTypeFieldEntry
    {
    public:
        std::string fname;
        TypeKey ftype;

        EntityTypeFieldEntry(std::string fname, TypeKey ftype) : fname(fname), ftype(ftype)
        {
            ;
        }
    };

    class StdEntityType : public EntityType
    {
    public:
        std::vector<EntityTypeFieldEntry> fields;
        bool hasvalidations;

        StdEntityType(TypeKey tkey, std::vector<EntityTypeFieldEntry> fields, bool hasvalidations) : EntityType(TypeTag::TYPE_STD_ENTITY, tkey), fields(fields), hasvalidations(hasvalidations)
        {
            ;
        }

        virtual ~StdEntityType()
        {
            ;
        }
    };

    class StdConceptType : public ConceptType
    {
    public:
        StdConceptType(TypeKey tkey, std::vector<TypeKey> subtypes) : ConceptType(TypeTag::TYPE_STD_CONCEPT, tkey, subtypes)
        {
            ;
        }

        virtual ~StdConceptType()
        {
            ;
        }
    };

    class PrimitiveType : public EntityType
    {
    public:
        PrimitiveType(TypeKey tkey) : EntityType(TypeTag::TYPE_PRIMITIVE, tkey)
        {
            ;
        }

        virtual ~PrimitiveType()
        {
            ;
        }
    };

    class EnumType : public EntityType
    {
    public:
        std::vector<std::string> variants;

        EnumType(TypeKey tkey, std::vector<std::string> variants) : EntityType(TypeTag::TYPE_ENUM, tkey), variants(variants)
        {
            ;
        }

        virtual ~EnumType()
        {
            ;
        }
    };

    class TypedeclType : public EntityType
    {
    public:
        TypeKey basetype;
        TypeKey oftype;

        std::optional<TypeKey> optStringOfValidator;
        std::optional<TypeKey> optPathOfValidator;
        bool hasvalidations;

        TypedeclType(TypeKey tkey, TypeKey basetype, TypeKey oftype, std::optional<TypeKey> optStringOfValidator, std::optional<TypeKey> optPathOfValidator, bool hasvalidations) : EntityType(TypeTag::TYPE_TYPE_DECL, tkey), basetype(basetype), oftype(oftype), optStringOfValidator(optStringOfValidator), optPathOfValidator(optPathOfValidator), hasvalidations(hasvalidations)
        {
            ;
        }

        virtual ~TypedeclType()
        {
            ;
        }
    };

    class ValidatorREType : public EntityType
    {
    public:
        ValidatorREType(TypeKey tkey) : EntityType(TypeTag::TYPE_VALIDATOR_RE, tkey)
        {
            ;
        }

        virtual ~ValidatorREType()
        {
            ;
        }
    };

    class ValidatorPthType : public EntityType
    {
    public: 
        ValidatorPthType(TypeKey tkey) : EntityType(TypeTag::TYPE_VALIDATOR_PTH, tkey)
        {
            ;
        }

        virtual ~ValidatorPthType()
        {
            ;
        }
    };

    class StringOfType : public EntityType
    {
    public:
        TypeKey oftype;

        StringOfType(TypeKey oftype) : EntityType(TypeTag::TYPE_STRING_OF, "StringOf<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~StringOfType()
        {
            ;
        }
    };

    class ASCIIStringOfType : public EntityType
    {
    public:
        TypeKey oftype;

        ASCIIStringOfType(TypeKey oftype) : EntityType(TypeTag::TYPE_ASCII_STRING_OF, "ASCIIStringOf<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~ASCIIStringOfType()
        {
            ;
        }
    };

    class SomethingType : public EntityType
    {
    public:
        TypeKey oftype;

        SomethingType(TypeKey oftype) : EntityType(TypeTag::TYPE_SOMETHING, "Something<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~SomethingType()
        {
            ;
        }
    };

    class OptionType : public ConceptType
    {
    public:
        TypeKey oftype;

        OptionType(TypeKey oftype) : ConceptType(TypeTag::TYPE_OPTION, "Option<" + oftype + ">", { "Nothing", "Something<" + oftype + ">" }), oftype(oftype)
        {
            ;
        }

        virtual ~OptionType()
        {
            ;
        }
    };

    class OkType : public EntityType
    {
    public:
        TypeKey ttype;
        TypeKey etype;

        OkType(TypeKey ttype, TypeKey etype) : EntityType(TypeTag::TYPE_OK, "Result<" + ttype + ", " + etype + ">::Ok"), ttype(ttype), etype(etype)
        {
            ;
        }

        virtual ~OkType()
        {
            ;
        }
    };

    class ErrorType : public EntityType
    {
    public:
        TypeKey ttype;
        TypeKey etype;

        ErrorType(TypeKey ttype, TypeKey etype) : EntityType(TypeTag::TYPE_ERROR, "Result<" + ttype + ", " + etype + ">::Err"), ttype(ttype), etype(etype)
        {
            ;
        }

        virtual ~ErrorType()
        {
            ;
        }
    };

    class ResultType : public ConceptType
    {
    public:
        TypeKey ttype;
        TypeKey etype;

        ResultType(TypeKey ttype, TypeKey etype) : ConceptType(TypeTag::TYPE_RESULT, "Result<" + ttype + ", " + etype + ">", { "Result<" + ttype + ", " + etype + ">::Ok", "Result<" + ttype + ", " + etype + ">::Err" }), ttype(ttype), etype(etype)
        {
            ;
        }

        virtual ~ResultType()
        {
            ;
        }
    };

    class PathType : public EntityType
    {
    public:
        TypeKey oftype;

        PathType(TypeKey oftype) : EntityType(TypeTag::TYPE_PATH, "Path<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~PathType()
        {
            ;
        }
    };

    class PathFragmentType : public EntityType
    {
    public:
        TypeKey oftype;

        PathFragmentType(TypeKey oftype) : EntityType(TypeTag::TYPE_PATH_FRAGMENT, "PathFragment<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~PathFragmentType()
        {
            ;
        }
    };

    class PathGlobType : public EntityType
    {
    public:
        TypeKey oftype;

        PathGlobType(TypeKey oftype) : EntityType(TypeTag::TYPE_PATH_GLOB, "PathGlob<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~PathGlobType()
        {
            ;
        }
    };

    class ListType : public EntityType
    {
    public:
        TypeKey oftype;

        ListType(TypeKey oftype) : EntityType(TypeTag::TYPE_LIST, "List<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~ListType()
        {
            ;
        }
    };

    class StackType : public EntityType
    {
    public:
        TypeKey oftype;

        StackType(TypeKey oftype) : EntityType(TypeTag::TYPE_STACK, "Stack<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~StackType()
        {
            ;
        }
    };

    class QueueType : public EntityType
    {
    public:
        TypeKey oftype;

        QueueType(TypeKey oftype) : EntityType(TypeTag::TYPE_QUEUE, "Queue<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~QueueType()
        {
            ;
        }
    };

    class SetType : public EntityType
    {
    public:
        TypeKey oftype;

        SetType(TypeKey oftype) : EntityType(TypeTag::TYPE_SET, "Set<" + oftype + ">"), oftype(oftype)
        {
            ;
        }

        virtual ~SetType()
        {
            ;
        }
    };

    class MapEntryType : public EntityType
    {
    public:
        TypeKey ktype;
        TypeKey vtype;

        MapEntryType(TypeKey ktype, TypeKey vtype) : EntityType(TypeTag::TYPE_MAP_ENTRY, "MapEntry<" + ktype + ", " + vtype + ">"), ktype(ktype), vtype(vtype)
        {
            ;
        }

        virtual ~MapEntryType()
        {
            ;
        }
    };

    class MapType : public EntityType
    {
    public:
        TypeKey ktype;
        TypeKey vtype;

        MapType(TypeKey ktype, TypeKey vtype) : EntityType(TypeTag::TYPE_MAP, "Map<" + ktype + ", " + vtype + ">"), ktype(ktype), vtype(vtype)
        {
            ;
        }

        virtual ~MapType()
        {
            ;
        }
    };

    class ConceptSetType : public Type
    {
    public:
        std::vector<TypeKey> concepts;

        ConceptSetType(std::vector<TypeKey> concepts) : Type(TypeTag::TYPE_CONCEPT_SET, std::accumulate(concepts.begin(), concepts.end(), std::string(), [](std::string& a, TypeKey& b) { return a + "&" + b; })), concepts(concepts)
        {
            ;
        }

        virtual ~ConceptSetType()
        {
            ;
        }  
    };

    class UnionType : public Type
    {
    public:
        std::vector<TypeKey> types;

        UnionType(std::vector<TypeKey> types) : Type(TypeTag::TYPE_UNION, std::accumulate(types.begin(), types.end(), std::string(), [](std::string& a, TypeKey& b) { return a + " | " + b; })), types(types)
        {
            ;
        }

        virtual ~UnionType()
        {
            ;
        }
    };

    class NamespaceDecl
    {
    public:
        std::string ns;
        std::vector<TypeKey> typenames;

        NamespaceDecl(std::string ns, std::vector<TypeKey> typenames) : ns(ns), typenames(typenames)
        {
            ;
        }

        static NamespaceDecl* parse(json j);

        bool hasTypenameDecl(const UnicodeString& name) const
        {
            return std::binary_search(this->typenames.begin(), this->typenames.end(), name);
        }
    };

    class AssemblyInfo
    {
    public:
        std::map<TypeKey, Type*> aliasmap;
        std::map<std::string, NamespaceDecl*> namespaces;
        std::map<TypeKey, Type*> typerefs;
        std::map<TypeKey, std::string> revalidators;
        std::map<TypeKey, std::string> pthvalidators;
        std::vector<std::set<TypeKey>> recursiveSets;

        AssemblyInfo()
        {
            ;
        }

        ~AssemblyInfo()
        {
            //
            //Should only be one assembly when executing -- so just let it hang out and get collected on shutdown
            //
        }

        static void parse(json j, AssemblyInfo& assembly);

        bool checkConcreteSubtype(Type* t, Type* oftype)
        {
            if (t->tkey == oftype->tkey)
            {
                return true;
            }

            if (oftype->tag == TypeTag::TYPE_UNION)
            {
                return std::any_of(static_cast<UnionType*>(oftype)->types.begin(), static_cast<UnionType*>(oftype)->types.end(), [this, t](TypeKey& tt) { return this->checkConcreteSubtype(t, this->typerefs[tt]); });
            }
            else if (oftype->tag == TypeTag::TYPE_CONCEPT_SET)
            {
                return std::all_of(static_cast<ConceptSetType*>(oftype)->concepts.begin(), static_cast<ConceptSetType*>(oftype)->concepts.end(), [this, t](TypeKey& tt) { return this->checkConcreteSubtype(t, this->typerefs[tt]); });
            }
            else 
            {
                auto psubtypes = oftype->getPossibleSubtypeKeys();
                if(psubtypes == nullptr)
                {
                    return false;
                }
                else
                {
                    return std::binary_search(psubtypes->begin(), psubtypes->end(), t->tkey);
                }
            }
        }

        Type* resolveType(TypeKey tkey)
        {
            auto tt = this->typerefs.find(tkey);
            if(tt != this->typerefs.end())
            {
                return tt->second;
            }
            else
            {
                return UnresolvedType::singleton;
            }
        }
    };

    void loadAssembly(json j);

    bool isSubtype(TypeKey tkey, TypeKey oftype);
}
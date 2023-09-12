
#include "type_info.h"

namespace BSQON 
{
    static AssemblyInfo g_assembly;

    Type* Type::parse(json j)
    {
        switch(j["tag"].get<TypeTag>()) {
            case TypeTag::TYPE_TUPLE: {
                std::vector<TypeKey> entries;
                std::transform(j["entries"].begin(), j["entries"].end(), std::back_inserter(entries), [](const json& jv) { return jv.get<TypeKey>(); });
                return new TupleType(entries);
            }
            case TypeTag::TYPE_RECORD: {
                std::vector<RecordTypeEntry> entries;
                std::transform(j["entries"].begin(), j["entries"].end(), std::back_inserter(entries), [](const json& jv) { 
                    return RecordTypeEntry(jv["pname"].get<std::string>(), jv["ptype"].get<TypeKey>()); 
                });
                return new RecordType(entries);
            }
            case TypeTag::TYPE_STD_ENTITY: {
                std::vector<EntityTypeFieldEntry> fields;
                std::transform(j["fields"].begin(), j["fields"].end(), std::back_inserter(fields), [](const json& jv) { 
                    return EntityTypeFieldEntry(jv["fname"].get<std::string>(), jv["ftype"].get<TypeKey>()); 
                });
                return new StdEntityType(j["tkey"].get<TypeKey>(), fields, j["hasvalidations"].get<bool>());
            }
            case TypeTag::TYPE_STD_CONCEPT: {
                std::vector<TypeKey> subtypes;
                std::transform(j["subtypes"].begin(), j["subtypes"].end(), std::back_inserter(subtypes), [](const json& jv) { return jv.get<TypeKey>(); });
                return new StdConceptType(j["tkey"].get<TypeKey>(), subtypes);
            }
            case TypeTag::TYPE_PRIMITIVE: {
                return new PrimitiveType(j["tkey"].get<TypeKey>());
            }
            case TypeTag::TYPE_ENUM: {
                std::vector<std::string> variants;
                std::transform(j["variants"].begin(), j["variants"].end(), std::back_inserter(variants), [](const json& jv) { return jv.get<std::string>(); });
                return new EnumType(j["tkey"].get<TypeKey>(), variants);
            }
            case TypeTag::TYPE_TYPE_DECL: {
                std::optional<TypeKey> optStringOfValidator = !j["optStringOfValidator"].is_null() ? std::make_optional(j["optStringOfValidator"].get<std::string>()) : std::nullopt;
                std::optional<TypeKey> optPathOfValidator = !j["optPathOfValidator"].is_null() ? std::make_optional(j["optPathOfValidator"].get<std::string>()) : std::nullopt;

                return new TypedeclType(j["tkey"].get<TypeKey>(), j["basetype"].get<TypeKey>(), j["oftype"].get<TypeKey>(), optStringOfValidator, optPathOfValidator, j["hasvalidations"].get<bool>());
            }
            case TypeTag::TYPE_VALIDATOR_RE: {
                return new ValidatorREType(j["tkey"].get<TypeKey>());
            }
            case TypeTag::TYPE_VALIDATOR_PTH: {
                return new ValidatorPthType(j["tkey"].get<TypeKey>());
            }
            case TypeTag::TYPE_STRING_OF: {
                return new StringOfType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_ASCII_STRING_OF: {
                return new ASCIIStringOfType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_SOMETHING: {
                return new SomethingType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_OPTION: {
                return new OptionType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_OK: {
                return new OkType(j["ttype"].get<TypeKey>(), j["etype"].get<TypeKey>());
            }
            case TypeTag::TYPE_ERROR: {
                return new ErrorType(j["ttype"].get<TypeKey>(), j["etype"].get<TypeKey>());
            }
            case TypeTag::TYPE_RESULT: {
                return new ResultType(j["ttype"].get<TypeKey>(), j["etype"].get<TypeKey>());
            }
            case TypeTag::TYPE_PATH: {
                return new PathType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_PATH_FRAGMENT: {
                return new PathFragmentType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_PATH_GLOB: {
                return new PathGlobType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_LIST: {
                return new ListType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_STACK: {
                return new StackType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_QUEUE: {
                return new QueueType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_SET: {
                return new SetType(j["oftype"].get<TypeKey>());
            }
            case TypeTag::TYPE_MAP_ENTRY: {
                return new MapEntryType(j["ktype"].get<TypeKey>(), j["vtype"].get<TypeKey>());
            }
            case TypeTag::TYPE_MAP: {
                return new MapType(j["ktype"].get<TypeKey>(), j["vtype"].get<TypeKey>());
            }
            case TypeTag::TYPE_CONCEPT_SET: {
                std::vector<TypeKey> concepts;
                std::transform(j["concepts"].begin(), j["concepts"].end(), std::back_inserter(concepts), [](const json& jv) { return jv.get<TypeKey>(); });
                return new ConceptSetType(concepts);
            }
            case TypeTag::TYPE_UNION: {
                std::vector<TypeKey> types;
                std::transform(j["types"].begin(), j["types"].end(), std::back_inserter(types), [](const json& jv) { return jv.get<TypeKey>(); });
                return new UnionType(types);
            }
            default: {
                return UnresolvedType::singleton;
            }
        }
    }

    UnresolvedType* UnresolvedType::singleton = new UnresolvedType();

    NamespaceDecl* NamespaceDecl::parse(json j)
    {
        std::vector<TypeKey> typenames;
        std::transform(j["typenames"].begin(), j["typenames"].end(), std::back_inserter(typenames), [](const json& jv) { return jv.get<TypeKey>(); });

        return new NamespaceDecl(j["ns"].get<std::string>(), typenames);
    }

    void AssemblyInfo::parse(json j, AssemblyInfo& assembly)
    {
        std::for_each(j["namespaces"].begin(), j["namespaces"].end(), [&assembly](const json &ns) { 
            auto nsd = NamespaceDecl::parse(ns);
            assembly.namespaces[nsd->ns] = nsd; 
        });

        std::for_each(j["typerefs"].begin(), j["typerefs"].end(), [&assembly](const json &tr) { 
            auto t = Type::parse(tr);
            assembly.typerefs[t->tkey] = t; 
        });

        std::for_each(j["aliasmap"].begin(), j["aliasmap"].end(), [&assembly](const json &a) { 
            assembly.aliasmap[a[0].get<std::string>()] = assembly.typerefs[a[1].get<TypeKey>()];
        });

        std::for_each(j["revalidators"].begin(), j["revalidators"].end(), [&assembly](const json &rv) {
            assembly.revalidators[rv[0].get<TypeKey>()] = rv[1].get<std::string>();
        });

        std::for_each(j["pthvalidators"].begin(), j["pthvalidators"].end(), [&assembly](const json &pv) {
            assembly.pthvalidators[pv[0].get<TypeKey>()] = pv[1].get<std::string>();
        });

        std::for_each(j["recursiveSets"].begin(), j["recursiveSets"].end(), [&assembly](const json &rs) { 
            std::set<TypeKey> rset;
            std::transform(rs.begin(), rs.end(), std::inserter(rset, rset.end()), [](const json& jv) { return jv.get<TypeKey>(); });
            assembly.recursiveSets.push_back(rset);
        });
    }

    void loadAssembly(json j)
    {
        AssemblyInfo::parse(j, g_assembly);
    }

    bool isSubtype(TypeKey tkey, TypeKey oftype)
    {
        auto t = g_assembly.typerefs[tkey];
        auto uu = g_assembly.typerefs[oftype];

        return g_assembly.checkConcreteSubtype(t, uu);
    }
}

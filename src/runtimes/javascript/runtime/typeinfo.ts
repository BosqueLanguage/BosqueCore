
type BSQTypeKey = string;

enum BSQTypeTag {
    TYPE_UNRESOLVED = "UnresolvedType",
    TYPE_TUPLE = "[...]",
    TYPE_RECORD = "{...}",
    TYPE_STD_ENTITY = "StdEntity",
    TYPE_STD_CONCEPT = "StdConcept",
    TYPE_PRIMITIVE = "PrimitiveEntity",
    TYPE_ENUM = "EnumEntity",
    TYPE_TYPE_DECL = "TypeDecl",
    TYPE_VALIDATOR_RE = "ValidatorRE",
    TYPE_VALIDATOR_PTH = "ValidatorPth",
    TYPE_STRING_OF = "StringOf",
    TYPE_ASCII_STRING_OF = "AsciiStringOf",
    TYPE_SOMETHING = "Something",
    TYPE_OPTION = "Option",
    TYPE_OK = "Result::Ok",
    TYPE_ERROR = "Result::Error",
    TYPE_RESULT = "Result",
    TYPE_PATH = "Path",
    TYPE_PATH_FRAGMENT = "PathFragment",
    TYPE_PATH_GLOB = "PathGlob",
    TYPE_LIST = "List",
    TYPE_STACK = "Stack",
    TYPE_QUEUE = "Queue",
    TYPE_SET = "Set",
    TYPE_MAP_ENTRY = "MapEntry",
    TYPE_MAP = "Map",
    TYPE_CONCEPT_SET = "ConceptSet",
    TYPE_UNION = "UnionType"
};

abstract class BSQType {
    readonly tag: BSQTypeTag;
    readonly tkey: BSQTypeKey;

    readonly isrecursive: boolean;
    readonly isconcretetype: boolean;

    constructor(tag: BSQTypeTag, tkey: BSQTypeKey, isrecursive: boolean, isconcretetype: boolean) {
        this.tag = tag;
        this.tkey = tkey;

        this.isrecursive = isrecursive;
        this.isconcretetype = isconcretetype;
    }
}

class UnresolvedType extends BSQType {
    constructor() {
        super(BSQTypeTag.TYPE_UNRESOLVED, "[UNRESOLVED]", false, true);
    }

    static readonly singleton = new UnresolvedType();
}

class TupleType extends BSQType {
    readonly entries: BSQTypeKey[];

    constructor(entries: BSQTypeKey[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_TUPLE, `[${entries.map((entry) => entry).join(", ")}]`, isrecursive, true);
        this.entries = entries;
    }
}

class RecordType extends BSQType {
    readonly entries: {pname: string, rtype: BSQTypeKey}[];

    constructor(entries: {pname: string, rtype: BSQTypeKey}[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_RECORD, `{${entries.map((entry) => `${entry.pname}: ${entry.rtype}`).join(", ")}}`, isrecursive, true);
        this.entries = entries;
    }
}

abstract class EntityType extends BSQType {
    constructor(tag: BSQTypeTag, tkey: BSQTypeKey, isrecursive: boolean) {
        super(tag, tkey, isrecursive, true);
    }
}

abstract class ConceptType extends BSQType {
    readonly subtypes: Set<BSQTypeKey>;

    constructor(tag: BSQTypeTag, tkey: BSQTypeKey, subtypes: Set<BSQTypeKey>, isrecursive: boolean) {
        super(tag, tkey, isrecursive, false);
        this.subtypes = subtypes;
    }
}

class StdEntityType extends EntityType {
    readonly hasvalidations: boolean;
    readonly fields: {fname: string, ftype: BSQTypeKey}[];

    constructor(tkey: BSQTypeKey, hasvalidations: boolean, fields: {fname: string, ftype: BSQTypeKey}[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_STD_ENTITY, tkey, isrecursive);

        this.hasvalidations = hasvalidations;
        this.fields = fields;
    }
}

class StdConceptType extends ConceptType {
    constructor(tkey: BSQTypeKey, subtypes: Set<BSQTypeKey>, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_STD_CONCEPT, tkey, subtypes, isrecursive);
    }
}

class PrimitiveType extends EntityType {
    constructor(tkey: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PRIMITIVE, tkey, false);
    }
}

class EnumType extends EntityType {
    readonly variants: string[];

    constructor(tkey: BSQTypeKey, variants: string[]) {
        super(BSQTypeTag.TYPE_ENUM, tkey, false);

        this.variants = variants;
    }
}

class TypedeclType extends EntityType {
    readonly basetype: BSQTypeKey;
    readonly oftype: BSQTypeKey;

    readonly hasvalidations: boolean;
    readonly optStringOfValidator: BSQTypeKey | undefined;
    readonly optPathOfValidator: BSQTypeKey | undefined;

    constructor(tkey: BSQTypeKey, basetype: BSQTypeKey, oftype: BSQTypeKey, isrecursive: boolean, hasvalidations: boolean, optStringOfValidator: BSQTypeKey | undefined, optPathOfValidator: BSQTypeKey | undefined) {
        super(BSQTypeTag.TYPE_TYPE_DECL, tkey, isrecursive);

        this.basetype = basetype;
        this.oftype = oftype;

        this.hasvalidations = hasvalidations;
        this.optStringOfValidator = optStringOfValidator;
        this.optPathOfValidator = optPathOfValidator;
    }
}

class ValidatorREType extends EntityType {
    constructor(tkey: BSQTypeKey) {
        super(BSQTypeTag.TYPE_VALIDATOR_RE, tkey, false);
    }
}

class ValidatorPthType extends EntityType {
    constructor(tkey: BSQTypeKey) {
        super(BSQTypeTag.TYPE_VALIDATOR_PTH, tkey, false);
    }
}

class StringOfType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_STRING_OF, `StringOf<${oftype}>`, false);
        this.oftype = oftype;
    }
}

class ASCIIStringOfType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_ASCII_STRING_OF, `ASCIIStringOf<${oftype}>`, false);
        this.oftype = oftype;
    }
}

class SomethingType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_SOMETHING, `Something<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }
}

class OptionType extends ConceptType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_OPTION, `Option<${oftype}>`, new Set(["Nothing", `Something<${oftype}>`]), isrecursive);
        this.oftype = oftype;
    }
}

class OkType extends EntityType {
    readonly ttype: BSQTypeTag;
    readonly etype: BSQTypeTag;

    constructor(ttype: BSQTypeTag, etype: BSQTypeTag, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_OK, `Result<${ttype}, ${etype}>::Ok`, isrecursive);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class ErrorType extends EntityType {
    readonly ttype: BSQTypeTag;
    readonly etype: BSQTypeTag;

    constructor(ttype: BSQTypeTag, etype: BSQTypeTag, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_ERROR, `Result<${ttype}, ${etype}>::Error`, isrecursive);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class ResultType extends ConceptType {
    readonly ttype: BSQTypeKey;
    readonly etype: BSQTypeKey;

    constructor(ttype: BSQTypeKey, etype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_RESULT, `Result<${ttype}, ${etype}>`, new Set([`Result<${ttype}, ${etype}>::Ok`, `Result<${ttype}, ${etype}>::Err`]), isrecursive);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class PathType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PATH, `Path<${oftype}>`, false);
        this.oftype = oftype;
    }
}

class PathFragmentType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PATH_FRAGMENT, `PathFragment<${oftype}>`, false);
        this.oftype = oftype;
    }
}

class PathGlobType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PATH_GLOB, `PathGlob<${oftype}>`, false);
        this.oftype = oftype;
    }
}

class ListType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_LIST, `List<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }
}

class StackType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_STACK, `Stack<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }
}

class QueueType extends EntityType {
    readonly oftype: BSQTypeKey;
    
    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_QUEUE, `Queue<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }
}

class SetType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_SET, `Set<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }
}

class MapEntryType extends EntityType {
    readonly ktype: BSQTypeKey;
    readonly vtype: BSQTypeKey;

    constructor(ktype: BSQTypeKey, vtype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_MAP_ENTRY, `MapEntry<${ktype}, ${vtype}>`, isrecursive);
        this.ktype = ktype;
        this.vtype = vtype;
    }
}

class MapType extends EntityType {
    readonly ktype: BSQTypeKey;
    readonly vtype: BSQTypeKey;

    constructor(ktype: BSQTypeKey, vtype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_MAP, `Map<${ktype}, ${vtype}>`, isrecursive);
        this.ktype = ktype;
        this.vtype = vtype;
    }
}

class ConceptSetType extends BSQType {
    readonly concepts: BSQTypeKey[];
    readonly subtypes: Set<BSQTypeKey>;

    constructor(concepts: BSQTypeKey[], subtypes: Set<BSQTypeKey>, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_CONCEPT_SET, concepts.map((cc) => cc).sort().join("&"), isrecursive, false);

        this.concepts = concepts;
        this.subtypes = subtypes;
    }
}

class UnionType extends BSQType {
    readonly types: BSQTypeKey[];

    constructor(types: BSQTypeKey[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_UNION, types.map((tt) => tt).sort().join(" | "), isrecursive, false);
        this.types = types;
    }
}

class NamespaceDecl {
    readonly ns: string;
    readonly typenames: BSQTypeKey[];

    constructor(ns: string, typenames: BSQTypeKey[]) {
        this.ns = ns;
        this.typenames = typenames;
    }
}

class AssemblyInfo {
    readonly aliasmap: Map<string, BSQType>;
    readonly namespaces: Map<string, NamespaceDecl>;
    readonly typerefs: Map<BSQTypeKey, BSQType>;
    readonly revalidators: Map<BSQTypeKey, string>;
    readonly pthvalidators: Map<BSQTypeKey, string>;

    constructor(aliasmap: Map<string, BSQType>, namespaces: Map<string, NamespaceDecl>, typerefs: Map<string, BSQType>, revalidators: Map<BSQTypeKey, string>, pthvalidators: Map<BSQTypeKey, string>) {
        this.aliasmap = aliasmap;
        this.namespaces = namespaces;
        this.typerefs = typerefs;
        this.revalidators = revalidators;
        this.pthvalidators = pthvalidators;
    }

    resolveTypeWithCoreOrDefault(tname: string, inns: string): BSQType {
        const cc = this.namespaces.get("Core") as NamespaceDecl;
        if(cc.typenames.includes(tname)) {
            return this.typerefs.get(tname) as BSQType;
        }
        else {
            const ns = this.namespaces.get(inns) as NamespaceDecl;
            if(ns.typenames.includes(tname)) {
                return this.typerefs.get(`${inns}::${tname}`) as BSQType;
            }
            else {
                return UnresolvedType.singleton;
            }
        }
    }

    checkConcreteSubtype(t: BSQType, oftype: BSQType): boolean {
        if (t.tkey === oftype.tkey) {
            return true;
        }

        if(oftype instanceof UnionType) {
            return oftype.types.some((tt) => this.checkConcreteSubtype(t, this.typerefs.get(tt) as BSQType));
        }
        else if(oftype instanceof ConceptType) {
            return oftype.subtypes.has(t.tkey);
        }
        else if(oftype instanceof ConceptSetType) {
            return oftype.subtypes.has(t.tkey);
        }
        else {
            return false;
        }
    }
}


let loaded_typeinfo: AssemblyInfo | undefined = undefined;
function isSubtype_Runtime(tkey: BSQTypeKey, oftype: BSQTypeKey): boolean {
    let lasm = loaded_typeinfo as AssemblyInfo;
    let t = lasm.typerefs.get(tkey) as BSQType;
    let uu = lasm.typerefs.get(oftype) as BSQType;
    return lasm.checkConcreteSubtype(t, uu);
}

export {
    BSQTypeKey, BSQTypeTag, 
    BSQType, UnresolvedType, TupleType, RecordType, EntityType, ConceptType, StdEntityType, StdConceptType, 
    PrimitiveType, EnumType, TypedeclType, ValidatorREType, ValidatorPthType, 
    StringOfType, ASCIIStringOfType, SomethingType, OptionType, OkType, ErrorType, ResultType, PathType, PathFragmentType, PathGlobType,
    ListType, StackType, QueueType, SetType, MapEntryType, MapType,
    ConceptSetType, UnionType, NamespaceDecl, AssemblyInfo,
    loaded_typeinfo, isSubtype_Runtime
}


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
    TYPE_ERROR = "Result::Err",
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

    abstract emit(): any;
    static parse(jv: any): BSQType {
        switch(jv.tag) {
            case BSQTypeTag.TYPE_TUPLE: {
                return new TupleType(jv.entries, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_RECORD: {
                return new RecordType(jv.entries, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_STD_ENTITY: {
                return new StdEntityType(jv.tkey, jv.hasvalidations, jv.fields, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_STD_CONCEPT: {
                return new StdConceptType(jv.tkey, jv.subtypes, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_PRIMITIVE: {
                return new PrimitiveType(jv.tkey);
            }
            case BSQTypeTag.TYPE_ENUM: {
                return new EnumType(jv.tkey, jv.variants);
            }
            case BSQTypeTag.TYPE_TYPE_DECL: {
                return new TypedeclType(jv.tkey, jv.basetype, jv.oftype, jv.isrecursive, jv.hasvalidations, jv.optStringOfValidator, jv.optPathOfValidator);
            }
            case BSQTypeTag.TYPE_VALIDATOR_RE: {
                return new ValidatorREType(jv.tkey);
            }
            case BSQTypeTag.TYPE_VALIDATOR_PTH: {
                return new ValidatorPthType(jv.tkey);
            }
            case BSQTypeTag.TYPE_STRING_OF: {
                return new StringOfType(jv.oftype);
            }
            case BSQTypeTag.TYPE_ASCII_STRING_OF: {
                return new ASCIIStringOfType(jv.oftype);
            }
            case BSQTypeTag.TYPE_SOMETHING: {
                return new SomethingType(jv.oftype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_OPTION: {
                return new OptionType(jv.oftype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_OK: {
                return new OkType(jv.ttype, jv.etype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_ERROR: {
                return new ErrorType(jv.ttype, jv.etype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_RESULT: {
                return new ResultType(jv.ttype, jv.etype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_PATH: {
                return new PathType(jv.oftype);
            }
            case BSQTypeTag.TYPE_PATH_FRAGMENT: {
                return new PathFragmentType(jv.oftype);
            }
            case BSQTypeTag.TYPE_PATH_GLOB: {
                return new PathGlobType(jv.oftype);
            }
            case BSQTypeTag.TYPE_LIST: {
                return new ListType(jv.oftype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_STACK: {
                return new StackType(jv.oftype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_QUEUE: {
                return new QueueType(jv.oftype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_SET: {
                return new SetType(jv.oftype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_MAP_ENTRY: {
                return new MapEntryType(jv.ktype, jv.vtype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_MAP: {
                return new MapType(jv.ktype, jv.vtype, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_CONCEPT_SET: {
                return new ConceptSetType(jv.concepts, jv.subtypes, jv.isrecursive);
            }
            case BSQTypeTag.TYPE_UNION: {
                return new UnionType(jv.types, jv.isrecursive);
            }
            default: {
                return UnresolvedType.singleton;
            }
        }
    }
}

class UnresolvedType extends BSQType {
    constructor() {
        super(BSQTypeTag.TYPE_UNRESOLVED, "[UNRESOLVED]", false, true);
    }

    static readonly singleton = new UnresolvedType();

    emit(): any {
        return {tag: BSQTypeTag.TYPE_UNRESOLVED};
    }
}

class TupleType extends BSQType {
    readonly entries: BSQTypeKey[];

    constructor(entries: BSQTypeKey[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_TUPLE, `[${entries.map((entry) => entry).join(", ")}]`, isrecursive, true);
        this.entries = entries;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_TUPLE, entries: this.entries, isrecursive: this.isrecursive};
    }
}

class RecordType extends BSQType {
    readonly entries: {pname: string, ptype: BSQTypeKey}[];

    constructor(entries: {pname: string, ptype: BSQTypeKey}[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_RECORD, `{${entries.map((entry) => `${entry.pname}: ${entry.ptype}`).join(", ")}}`, isrecursive, true);
        this.entries = entries;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_RECORD, entries: this.entries, isrecursive: this.isrecursive};
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

    emit(): any {
        return {tag: BSQTypeTag.TYPE_STD_ENTITY, tkey: this.tkey, hasvalidations: this.hasvalidations, fields: this.fields, isrecursive: this.isrecursive};
    }
}

class StdConceptType extends ConceptType {
    constructor(tkey: BSQTypeKey, subtypes: BSQTypeKey[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_STD_CONCEPT, tkey, new Set<BSQTypeKey>(subtypes), isrecursive);
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_STD_CONCEPT, tkey: this.tkey, subtypes: [...this.subtypes], isrecursive: this.isrecursive};
    }
}

class PrimitiveType extends EntityType {
    constructor(tkey: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PRIMITIVE, tkey, false);
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_PRIMITIVE, tkey: this.tkey};
    }
}

class EnumType extends EntityType {
    readonly variants: string[];

    constructor(tkey: BSQTypeKey, variants: string[]) {
        super(BSQTypeTag.TYPE_ENUM, tkey, false);

        this.variants = variants;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_ENUM, tkey: this.tkey, variants: this.variants};
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

    emit(): any {
        return {tag: BSQTypeTag.TYPE_TYPE_DECL, tkey: this.tkey, basetype: this.basetype, oftype: this.oftype, isrecursive: this.isrecursive, hasvalidations: this.hasvalidations, optStringOfValidator: this.optStringOfValidator, optPathOfValidator: this.optPathOfValidator};
    }
}

class ValidatorREType extends EntityType {
    constructor(tkey: BSQTypeKey) {
        super(BSQTypeTag.TYPE_VALIDATOR_RE, tkey, false);
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_VALIDATOR_RE, tkey: this.tkey};
    }
}

class ValidatorPthType extends EntityType {
    constructor(tkey: BSQTypeKey) {
        super(BSQTypeTag.TYPE_VALIDATOR_PTH, tkey, false);
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_VALIDATOR_PTH, tkey: this.tkey};
    }
}

class StringOfType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_STRING_OF, `StringOf<${oftype}>`, false);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_STRING_OF, oftype: this.oftype};
    }
}

class ASCIIStringOfType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_ASCII_STRING_OF, `ASCIIStringOf<${oftype}>`, false);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_ASCII_STRING_OF, oftype: this.oftype};
    }
}

class SomethingType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_SOMETHING, `Something<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_SOMETHING, oftype: this.oftype, isrecursive: this.isrecursive};
    }
}

class OptionType extends ConceptType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_OPTION, `Option<${oftype}>`, new Set(["Nothing", `Something<${oftype}>`]), isrecursive);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_OPTION, oftype: this.oftype, isrecursive: this.isrecursive};
    }
}

class OkType extends EntityType {
    readonly ttype: BSQTypeKey;
    readonly etype: BSQTypeKey;

    constructor(ttype: BSQTypeKey, etype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_OK, `Result<${ttype}, ${etype}>::Ok`, isrecursive);
        this.ttype = ttype;
        this.etype = etype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_OK, ttype: this.ttype, etype: this.etype, isrecursive: this.isrecursive};
    }
}

class ErrorType extends EntityType {
    readonly ttype: BSQTypeKey;
    readonly etype: BSQTypeKey;

    constructor(ttype: BSQTypeKey, etype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_ERROR, `Result<${ttype}, ${etype}>::Err`, isrecursive);
        this.ttype = ttype;
        this.etype = etype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_ERROR, ttype: this.ttype, etype: this.etype, isrecursive: this.isrecursive};
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

    emit(): any {
        return {tag: BSQTypeTag.TYPE_RESULT, ttype: this.ttype, etype: this.etype, isrecursive: this.isrecursive};
    }
}

class PathType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PATH, `Path<${oftype}>`, false);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_PATH, oftype: this.oftype};
    }
}

class PathFragmentType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PATH_FRAGMENT, `PathFragment<${oftype}>`, false);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_PATH_FRAGMENT, oftype: this.oftype};
    }
}

class PathGlobType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey) {
        super(BSQTypeTag.TYPE_PATH_GLOB, `PathGlob<${oftype}>`, false);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_PATH_GLOB, oftype: this.oftype};
    }
}

class ListType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_LIST, `List<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_LIST, oftype: this.oftype, isrecursive: this.isrecursive};
    }
}

class StackType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_STACK, `Stack<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_STACK, oftype: this.oftype, isrecursive: this.isrecursive};
    }
}

class QueueType extends EntityType {
    readonly oftype: BSQTypeKey;
    
    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_QUEUE, `Queue<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_QUEUE, oftype: this.oftype, isrecursive: this.isrecursive};
    }
}

class SetType extends EntityType {
    readonly oftype: BSQTypeKey;

    constructor(oftype: BSQTypeKey, isrecursive: boolean) {
        super(BSQTypeTag.TYPE_SET, `Set<${oftype}>`, isrecursive);
        this.oftype = oftype;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_SET, oftype: this.oftype, isrecursive: this.isrecursive};
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

    emit(): any {
        return {tag: BSQTypeTag.TYPE_MAP_ENTRY, ktype: this.ktype, vtype: this.vtype, isrecursive: this.isrecursive};
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

    emit(): any {
        return {tag: BSQTypeTag.TYPE_MAP, ktype: this.ktype, vtype: this.vtype, isrecursive: this.isrecursive};
    }
}

class ConceptSetType extends BSQType {
    readonly concepts: BSQTypeKey[];
    readonly subtypes: Set<BSQTypeKey>;

    constructor(concepts: BSQTypeKey[], subtypes: BSQTypeKey[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_CONCEPT_SET, concepts.sort().join("&"), isrecursive, false);

        this.concepts = concepts;
        this.subtypes = new Set<BSQTypeKey>(subtypes);
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_CONCEPT_SET, concepts: this.concepts, subtypes: [...this.subtypes], isrecursive: this.isrecursive};
    }
}

class UnionType extends BSQType {
    readonly types: BSQTypeKey[];

    constructor(types: BSQTypeKey[], isrecursive: boolean) {
        super(BSQTypeTag.TYPE_UNION, types.sort().join(" | "), isrecursive, false);
        this.types = types;
    }

    emit(): any {
        return {tag: BSQTypeTag.TYPE_UNION, types: this.types, isrecursive: this.isrecursive};
    }
}

class NamespaceDecl {
    readonly ns: string;
    readonly typenames: BSQTypeKey[];

    constructor(ns: string, typenames: BSQTypeKey[]) {
        this.ns = ns;
        this.typenames = typenames;
    }

    emit(): any {
        return {ns: this.ns, typenames: this.typenames};
    }

    static parse(jv: any): NamespaceDecl {
        return new NamespaceDecl(jv.ns, jv.typenames);
    }
}

class AssemblyInfo {
    readonly aliasmap: Map<BSQTypeKey, BSQType>;
    readonly namespaces: Map<string, NamespaceDecl>;
    readonly typerefs: Map<BSQTypeKey, BSQType>;
    readonly revalidators: Map<BSQTypeKey, string>;
    readonly pthvalidators: Map<BSQTypeKey, string>;
    readonly recursiveSets: Set<BSQTypeKey>[];

    constructor(aliasmap: Map<string, BSQType>, namespaces: Map<string, NamespaceDecl>, typerefs: Map<string, BSQType>, revalidators: Map<BSQTypeKey, string>, pthvalidators: Map<BSQTypeKey, string>, recursiveSets: Set<BSQTypeKey>[]) {
        this.aliasmap = aliasmap;
        this.namespaces = namespaces;
        this.typerefs = typerefs;
        this.revalidators = revalidators;
        this.pthvalidators = pthvalidators;
        this.recursiveSets = recursiveSets;
    }

    emit(): any {
        return {
            aliasmap: [...this.aliasmap.entries()].map((e) => [e[0], e[1].tkey]),
            namespaces: [...this.namespaces.entries()].map((e) => e[1].emit()),
            typerefs: [...this.typerefs.entries()].map((e) => e[1].emit()),
            revalidators: [...this.revalidators.entries()],
            pthvalidators: [...this.pthvalidators.entries()],
            recursiveSets: this.recursiveSets.map((s) => [...s])
        };
    }

    static parse(jv: any): AssemblyInfo {
        const namespaces = new Map<string, NamespaceDecl>();
        jv.namespaces.forEach((ns: any) => {
            const nsd = NamespaceDecl.parse(ns);
            namespaces.set(nsd.ns, nsd);
        });

        const typerefs = new Map<string, BSQType>();
        jv.typerefs.forEach((tt: any) => {
            const t = BSQType.parse(tt);
            typerefs.set(t.tkey, t);
        });

        const aliasmap = new Map<string, BSQType>();
        jv.aliasmap.forEach((aa: any) => {
            aliasmap.set(aa[0], typerefs.get(aa[1]) as BSQType);
        });

        const revalidators = new Map<BSQTypeKey, string>();
        jv.revalidators.forEach((rv: any) => {
            revalidators.set(rv[0], rv[1]);
        });

        const pthvalidators = new Map<BSQTypeKey, string>();
        jv.pthvalidators.forEach((pv: any) => {
            pthvalidators.set(pv[0], pv[1]);
        });

        const recursiveSets: Set<BSQTypeKey>[] = [];
        jv.recursiveSets.forEach((rs: any) => {
            recursiveSets.push(new Set<BSQTypeKey>(rs));
        });

        return new AssemblyInfo(aliasmap, namespaces, typerefs, revalidators, pthvalidators, recursiveSets);
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

    loadType(tkey: BSQTypeKey): BSQType {
        return this.typerefs.get(tkey) as BSQType;
    }
}


let loaded_typeinfo: AssemblyInfo | undefined = undefined;
function setLoadedTypeInfo(lasm: AssemblyInfo): void {
    loaded_typeinfo = lasm;
}

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
    loaded_typeinfo, setLoadedTypeInfo, isSubtype_Runtime
}

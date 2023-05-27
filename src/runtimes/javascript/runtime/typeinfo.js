"use strict";

const TYPE_UNRESOLVED = "UnresolvedType";
const TYPE_TUPLE = "[...]";
const TYPE_RECORD = "{...}";
const TYPE_SIMPLE_ENTITY = "SimpleEntity";
const TYPE_SIMPLE_CONCEPT = "SimpleConcept";
const TYPE_STRING_OF = "StringOf";
const TYPE_ASCII_STRING_OF = "AsciiStringOf";
const TYPE_SOMETHING = "Something"; 
const TYPE_OPTION = "Option";
const TYPE_OK = "Result::Ok";
const TYPE_ERROR = "Result::Error";  
const TYPE_RESULT = "Result"; 
const TYPE_PATH = "Path";
const TYPE_PATH_FRAGMENT = "PathFragment";
const TYPE_PATH_GLOB = "PathGlob"; 
const TYPE_LIST = "List";
const TYPE_STACK = "Stack";
const TYPE_QUEUE = "Queue";
const TYPE_SET = "Set";
const TYPE_MAP_ENTRY = "MapEntry";
const TYPE_MAP = "Map";

const TYPE_CONCEPT_SET = "ConceptSet";
const TYPE_UNION = "UnionType";

const AMBIG_TYPES = new Set([TYPE_SIMPLE_CONCEPT, TYPE_OPTION, TYPE_RESULT, TYPE_CONCEPT_SET, TYPE_UNION]);

const RE_VALIDATOR_DECL = "StringValidator";
const PATH_VALIDATOR_DECL = "PathValidator";

const ENTITY_DECL = "EntityDecl";
const ENUM_DECL = "EnumDecl";
const TYPEDECL_DECL = "TypedeclDecl";
const CONCEPT_DECL = "ConceptDecl";

const unresolvedType = {tag: UNRESOLVED_TYPE, ttag: "[UnresolvedType]"};

function createTuple(entries, isrec) {
    return {tag: TYPE_TUPLE, isrec: isrec ?? false, ttag: entries.map((entry) => entry.ttag).join(", "), entries: entries};
}

function createRecord(entries, isrec) {
    return {tag: TYPE_RECORD, isrec: isrec ?? false, ttag: entries.keys().sort().map((kk) => kk + ": " + entries[kk].ttag).join(", "), entries: entries};
}

function createSimpleEntity(name, isrec) {
    return {tag: TYPE_SIMPLE_ENTITY, isrec: isrec ?? false, ttag: name};
}

function createSimpleConcept(name, isrec) {
    return {tag: TYPE_SIMPLE_CONCEPT, isrec: isrec ?? false, ttag: name};
}

function createStringOf(type, isrec) {
    return {tag: TYPE_STRING_OF, isrec: isrec ?? false, ttag: `StringOf<${type.ttag}>`, oftype: type};
}

function createASCIIStringOf(type, isrec) {
    return {tag: TYPE_ASCII_STRING_OF, isrec: isrec ?? false, ttag: `ASCIIStringOf<${type.ttag}>`, oftype: type};
}

function createSomething(type, isrec) {
    return {tag: TYPE_SOMETHING, isrec: isrec ?? false, ttag: `Something<${type.ttag}>`, oftype: type};
}

function createOption(type, isrec) {
    return {tag: TYPE_OPTION, isrec: isrec ?? false, ttag: `Option<${type.ttag}>`, oftype: type};
}

function createOk(ttype, etype, isrec) {
    return {tag: TYPE_OK, isrec: isrec ?? false, ttag: `Result<${ttype.ttag}, ${etype.ttag}>::Ok`, ttype: type, etype: etype};
}

function createError(ttype, etype, isrec) {
    return {tag: TYPE_ERROR, isrec: isrec ?? false, ttag: `Result<${ttype.ttag}, ${etype.ttag}>::Error`, ttype: type, etype: etype};
}

function createResult(ttype, etype, isrec) {
    return {tag: TYPE_RESULT, isrec: isrec ?? false, ttag: `Result<${ttype.ttag}, ${etype.ttag}>`, ttype: type, etype: etype};
}

function createPath(oftype, isrec) {
    return {tag: TYPE_PATH, isrec: isrec ?? false, ttag: `Path<${oftype.ttag}>`, oftype: oftype};
}

function createPathFragment(oftype, isrec) {
    return {tag: TYPE_PATH_FRAGMENT, isrec: isrec ?? false, ttag: `PathFragment<${oftype.ttag}>`, oftype: oftype};
}

function createPathGlob(oftype, isrec) {
    return {tag: TYPE_PATH_GLOB, isrec: isrec ?? false, ttag: `PathGlob<${oftype.ttag}>`, oftype: oftype};
}

function createList(oftype, isrec) {
    return {tag: TYPE_LIST, isrec: isrec ?? false, ttag: `List<${oftype.ttag}>`, oftype: oftype};
}

function createStack(oftype, isrec) {
    return {tag: TYPE_STACK, isrec: isrec ?? false, ttag: `Stack<${oftype.ttag}>`, oftype: oftype};
}

function createQueue(oftype, isrec) {
    return {tag: TYPE_QUEUE, isrec: isrec ?? false, ttag: `Queue<${oftype.ttag}>`, oftype: oftype};
}

function createSet(oftype, isrec) {
    return {tag: TYPE_SET, isrec: isrec ?? false, ttag: `Set<${oftype.ttag}>`, oftype: oftype};
}

function createMapEntry(ktype, vtype, isrec) {
    return {tag: TYPE_MAP_ENTRY, isrec: isrec ?? false, ttag: `MapEntry<${ktype.ttag}, ${vtype.ttag}>`, ktype: ktype, vtype: vtype};
}

function createMap(ktype, vtype, isrec) {
    return {tag: TYPE_MAP, isrec: isrec ?? false, ttag: `Map<${ktype.ttag}, ${vtype.ttag}>`, ktype: ktype, vtype: vtype};
}

function createConceptSet(concepts, isrec) {
    return {tag: TYPE_CONCEPT_SET, isrec: isrec ?? false, ttag: concepts.map((cc) => cc.ttag).sort().join(" & "), concepts: concepts};
}

function createUnion(types, isrec) {
    return {tag: TYPE_UNION, isrec: isrec ?? false, ttag: types.map((tt) => tt.ttag).sort().join(" | "), types: types};
}

function createStringValidatorDecl(svtype, vre) {
    return {tag: RE_VALIDATOR_DECL, type: svtype, vre: vre};
}

function createPathValidatorDecl(pvtype, pstr) {
    return {tag: PATH_VALIDATOR_DECL, type: pvtype, pstr: pstr};
}

function createEntityFieldDecl(fname, ftype) {
    return {name: fname, type: ftype};
}

function createEntityDecl(ntype, fields) {
    return {tag: ENTITY_DECL, type: ntype, fields: fields};
}

function createEnumDecl(ntype, variants) {
    return {tag: ENUM_DECL, type: ntype, variants: variants};
}

function createTypedeclDecl(ntype, oftype, basetype) {
    return {tag: TYPEDECL_DECL, type: ntype, oftype: oftype, basetype: basetype};
}

function createConceptDecl(ntype, subtypes) {
    return {tag: CONCEPT_DECL, type: ntype, subtypes: subtypes};
}

function createNamespace(ns, typenames) {
    return {ns: ns, typenames: typenames};
}

function createAssemblyInfo(namespaces, typerefs, rechks, pthchks, sdecls, edecls, tdecls, conceptdecls, aliasmap) {
    let types = new Map();
    typerefs.forEach((tr) => {
        types.set(tr.ttag, tr);
    });

    let revalidators = new Map();
    rechks.forEach((vv) => {
        revalidators.set(vv.type.ttag, [vv, new RegExp("^" + vv+ "$")]);
    });

    let pthvalidators = new Map();
    pthchks.forEach((vv) => {
        pthvalidators.set(vv.type.ttag, vv);
    });

    let simpledecls = new Map();
    sdecls.forEach((dd) => {
        simpledecls.set(dd.type.ttag, dd);
    });

    let enumdecls = new Map();
    edecls.forEach((dd) => {
        enumdecls.set(dd.type.ttag, dd);
    });

    let typedecls = new Map();
    tdecls.forEach((dd) => {
        typedecls.set(dd.type.ttag, dd);
    });

    let conceptdecls = new Map();
    cdecls.forEach((dd) => {
        conceptdecls.set(dd.type.ttag, dd);
    });

    return {
        namespaces: namespaces,
        types: types,
        revalidators: revalidators,
        pthvalidators: pthvalidators,
        simpledecls: simpledecls,
        enumdecls: enumdecls,
        typedecls: typedecls,
        conceptdecls: conceptdecls,
        aliasmap: aliasmap
    };
}

function resolveTypeInAssembly(asm, tname) {
    return asm.typerefs.has(tname) ?? unresolvedType;
}

function isTypeUniquelyResolvable(ttype) {
    return !AMBIG_TYPES.has(ttype.tag);
}

function checkSubtype(asm, t, oftype) {
    if(t.ttag === oftype.ttag) {
        return true;
    }

    if(oftype.tag === TYPE_SIMPLE_CONCEPT) {
        const optconcept = asm.conceptdecls.get(oftype.ttag);
        return optconcept !== undefined && optconcept.subtypes.has(t.ttag); 
    }
    else if(oftype.tag === TYPE_OPTION) {
        return t.ttag === "Nothing" || t.ttag === `Something<${oftype.oftype}>`;
    }
    else if(oftype.tag === TYPE_RESULT) {
        return t.ttag === `Result<${oftype.ttype}, ${oftype.etype}>::Ok` || t.ttag === `Result<${oftype.ttype}, ${oftype.etype}>::Error`;
    }
    else if(oftype.tag === TYPE_CONCEPT_SET) {
        return oftype.concepts.every((cc) => checkSubtype(asm, t, cc));
    }
    else if(oftype.tag === TYPE_UNION) {
        return oftype.types.some((tt) => checkSubtype(asm, t, tt));
    }
    else {
        return false;
    }
}

export {
    TYPE_UNRESOLVED,
    TYPE_TUPLE, TYPE_RECORD, TYPE_SIMPLE_ENTITY, TYPE_SIMPLE_CONCEPT,
    TYPE_STRING_OF, TYPE_ASCII_STRING_OF,
    TYPE_SOMETHING, TYPE_OPTION,
    TYPE_OK, TYPE_ERROR, TYPE_RESULT,
    TYPE_PATH, TYPE_PATH_FRAGMENT, TYPE_PATH_GLOB,
    TYPE_LIST, TYPE_STACK, TYPE_QUEUE, TYPE_SET, TYPE_MAP_ENTRY, TYPE_MAP,
    TYPE_CONCEPT_SET, TYPE_UNION,
    RE_VALIDATOR_DECL, PATH_VALIDATOR_DECL,
    ENTITY_DECL, ENUM_DECL, TYPEDECL_DECL, CONCEPT_DECL,
    unresolvedType,
    createTuple, createRecord, createSimpleEntity, createSimpleConcept,
    createStringOf, createASCIIStringOf,
    createSomething, createOption,
    createOk, createError, createResult,
    createPath, createPathFragment, createPathGlob,
    createList, createStack, createQueue, createSet, createMapEntry, createMap,
    createConceptSet, createUnion,
    createStringValidatorDecl, createPathValidatorDecl, 
    createEntityFieldDecl,
    createEntityDecl, createEnumDecl, createTypedeclDecl, createConceptDecl,
    createNamespace,
    createAssemblyInfo,
    resolveTypeInAssembly, isTypeUniquelyResolvable, checkSubtype
}

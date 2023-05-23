"use strict";

const TYPE_TUPLE = "[...]";
const TYPE_RECORD = "{...}";
const TYPE_SIMPLE_NOMINAL = "Type";
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

const RE_VALIDATOR_DECL = "StringValidator";
const PATH_VALIDATOR_DECL = "PathValidator";

const ENTITY_DECL = "EntityDecl";
const ENUM_DECL = "EnumDecl";
const TYPEDECL_DECL = "TypedeclDecl";
const CONCEPT_DECL = "ConceptDecl";

function createTuple(entries) {
    return {tag: TYPE_TUPLE, ttag: entries.map((entry) => entry.ttag).join(", "), entries: entries};
}

function createRecord(entries) {
    return {tag: TYPE_RECORD, ttag: entries.keys().sort().map((kk) => kk + ": " + entries[kk].ttag).join(", "), entries: entries};
}

function createSimpleNominal(name) {
    return {tag: TYPE_SIMPLE_NOMINAL, ttag: name};
}

function createStringOf(type) {
    return {tag: TYPE_STRING_OF, ttag: `StringOf<${type.ttag}>`, oftype: type};
}

function createAsciiStringOf(type) {
    return {tag: TYPE_ASCII_STRING_OF, ttag: `AsciiStringOf<${type.ttag}>`, oftype: type};
}

function createSomething(type) {
    return {tag: TYPE_SOMETHING, ttag: `Something<${type.ttag}>`, oftype: type};
}

function createOption(type) {
    return {tag: TYPE_OPTION, ttag: `Option<${type.ttag}>`, oftype: type};
}

function createOk(ttype, etype) {
    return {tag: TYPE_OK, ttag: `Result<${ttype.ttag}, ${etype.ttag}>::Ok`, ttype: type, etype: etype};
}

function createError(ttype, etype) {
    return {tag: TYPE_ERROR, ttag: `Result<${ttype.ttag}, ${etype.ttag}>::Error`, ttype: type, etype: etype};
}

function createResult(ttype, etype) {
    return {tag: TYPE_RESULT, ttag: `Result<${ttype.ttag}, ${etype.ttag}>`, ttype: type, etype: etype};
}

function createPath(oftype) {
    return {tag: TYPE_PATH, ttag: `Path<${oftype.ttag}>`, oftype: oftype};
}

function createPathFragment(oftype) {
    return {tag: TYPE_PATH_FRAGMENT, ttag: `PathFragment<${oftype.ttag}>`, oftype: oftype};
}

function createPathGlob(oftype) {
    return {tag: TYPE_PATH_GLOB, ttag: `PathGlob<${oftype.ttag}>`, oftype: oftype};
}

function createList(oftype) {
    return {tag: TYPE_LIST, ttag: `List<${oftype.ttag}>`, oftype: oftype};
}

function createStack(oftype) {
    return {tag: TYPE_STACK, ttag: `Stack<${oftype.ttag}>`, oftype: oftype};
}

function createQueue(oftype) {
    return {tag: TYPE_QUEUE, ttag: `Queue<${oftype.ttag}>`, oftype: oftype};
}

function createSet(oftype) {
    return {tag: TYPE_SET, ttag: `Set<${oftype.ttag}>`, oftype: oftype};
}

function createMapEntry(ktype, vtype) {
    return {tag: TYPE_MAP_ENTRY, ttag: `MapEntry<${ktype.ttag}, ${vtype.ttag}>`, ktype: ktype, vtype: vtype};
}

function createMap(ktype, vtype) {
    return {tag: TYPE_MAP, ttag: `Map<${ktype.ttag}, ${vtype.ttag}>`, ktype: ktype, vtype: vtype};
}

function createConceptSet(concepts) {
    return {tag: TYPE_CONCEPT_SET, ttag: concepts.map((cc) => cc.ttag).sort().join(" & "), concepts: concepts};
}

function createUnion(types) {
    return {tag: TYPE_UNION, ttag: types.map((tt) => tt.ttag).sort().join(" | "), types: types};
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

function createAssemblyInfo(typerefs, rechks, pthchks, sdecls, edecls, tdecls, conceptdecls, aliasmap) {
    let types = new Map();
    typerefs.forEach((tr) => {
        types.set(tr.ttag, tr);
    });

    let revalidators = new Map();
    rechks.forEach((vv) => {
        revalidators.set(vv.type.ttag, vv);
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

export {
    TYPE_TUPLE, TYPE_RECORD, TYPE_SIMPLE_NOMINAL,
    TYPE_STRING_OF, TYPE_ASCII_STRING_OF,
    TYPE_SOMETHING, TYPE_OPTION,
    TYPE_OK, TYPE_ERROR, TYPE_RESULT,
    TYPE_PATH, TYPE_PATH_FRAGMENT, TYPE_PATH_GLOB,
    TYPE_LIST, TYPE_STACK, TYPE_QUEUE, TYPE_SET, TYPE_MAP_ENTRY, TYPE_MAP,
    TYPE_CONCEPT_SET, TYPE_UNION,
    RE_VALIDATOR_DECL, PATH_VALIDATOR_DECL,
    ENTITY_DECL, ENUM_DECL, TYPEDECL_DECL, CONCEPT_DECL,
    createTuple, createRecord, createSimpleNominal,
    createStringOf, createAsciiStringOf,
    createSomething, createOption,
    createOk, createError, createResult,
    createPath, createPathFragment, createPathGlob,
    createList, createStack, createQueue, createSet, createMapEntry, createMap,
    createConceptSet, createUnion,
    createStringValidatorDecl, createPathValidatorDecl, 
    createEntityFieldDecl,
    createEntityDecl, createEnumDecl, createTypedeclDecl, createConceptDecl,
    createAssemblyInfo
}

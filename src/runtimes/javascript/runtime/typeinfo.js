"use strict";


const TYPE_TUPLE = "[...]";
const TYPE_RECORD = "{...}";
const TYPE_SIMPLE_NOMINAL = "T{...}";
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

function createTuple(entries) {
    return {type: TYPE_TUPLE, ttag: entries.map((entry) => entry.ttag).join(", "), entries: entries};
}

function createRecord(entries) {
    return {type: TYPE_RECORD, ttag: entries.map((entry) => entry[0] + ": " + entry[1].ttag).join(", "), entries: entries};
}

function createSimpleNominal(name) {
    return {type: TYPE_SIMPLE_NOMINAL, ttag: name};
}

function createStringOf(type) {
    return {type: TYPE_STRING_OF, ttag: `StringOf<${type.ttag}>`, oftype: type};
}

function createAsciiStringOf(type) {
    return {type: TYPE_ASCII_STRING_OF, ttag: `AsciiStringOf<${type.ttag}>`, oftype: type};
}

function createSomething(type) {
    return {type: TYPE_SOMETHING, ttag: `Something<${type.ttag}>`, oftype: type};
}

function createOption(type) {
    return {type: TYPE_OPTION, ttag: `Option<${type.ttag}>`, oftype: type};
}

function createOk(ttype, etype) {
    return {type: TYPE_OK, ttag: `Result<${ttype.ttag}, ${etype.ttag}>::Ok`, ttype: type, etype: etype};
}

function createError(ttype, etype) {
    return {type: TYPE_ERROR, ttag: `Result<${ttype.ttag}, ${etype.ttag}>::Error`, ttype: type, etype: etype};
}

function createResult(ttype, etype) {
    return {type: TYPE_RESULT, ttag: `Result<${ttype.ttag}, ${etype.ttag}>`, ttype: type, etype: etype};
}

function createPath(oftype) {
    return {type: TYPE_PATH, ttag: `Path<${oftype.ttag}>`, oftype: oftype};
}

function createPathFragment(oftype) {
    return {type: TYPE_PATH_FRAGMENT, ttag: `PathFragment<${oftype.ttag}>`, oftype: oftype};
}

function createPathGlob(oftype) {
    return {type: TYPE_PATH_GLOB, ttag: `PathGlob<${oftype.ttag}>`, oftype: oftype};
}

function createList(oftype) {
    return {type: TYPE_LIST, ttag: `List<${oftype.ttag}>`, oftype: oftype};
}

function createStack(oftype) {
    return {type: TYPE_STACK, ttag: `Stack<${oftype.ttag}>`, oftype: oftype};
}

function createQueue(oftype) {
    return {type: TYPE_QUEUE, ttag: `Queue<${oftype.ttag}>`, oftype: oftype};
}

function createSet(oftype) {
    return {type: TYPE_SET, ttag: `Set<${oftype.ttag}>`, oftype: oftype};
}

function createMapEntry(ktype, vtype) {
    return {type: TYPE_MAP_ENTRY, ttag: `MapEntry<${ktype.ttag}, ${vtype.ttag}>`, ktype: ktype, vtype: vtype};
}

function createMap(ktype, vtype) {
    return {type: TYPE_MAP, ttag: `Map<${ktype.ttag}, ${vtype.ttag}>`, ktype: ktype, vtype: vtype};
}

function createEntityFieldDecl(fname, ftype) {
    return {name: fname, type: ftype};
}

function createEntityDecl(ntype, fields) {
    return {type: ntype, fields: fields};
}

function createConceptDecl(ntype, subtypes) {
    return {type: ntype, subtypes: subtypes};
}

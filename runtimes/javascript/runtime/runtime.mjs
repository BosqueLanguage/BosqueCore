"use strict";

function BoxedValue(btype, bvalue) {
    this.btype = btype;
    this.btype = bvalue;
}

function Unwind(kind, msg) {
    this.kind = kind;
    this.msg = msg;
}

function createRuntimeError(msg) {
    return Unwind("error", msg);
}

function checkOk(cond, err, value) {
    if(!cond) {
        throw err;
    }

    return value;
}

function BType(tkey, vtable, consts, functions, methods, fdisplay, feq, fless) {
    this.tkey = tkey;
    this.vtable = vtable; //record
    this.consts = consts; //record
    this.functions = functions; //record
    this.methods = methods; //record
    this.fdisplay = fdisplay;
    this.feq = feq;
    this.fless = fless;
}

const BTypeNone = new BType("None", {}, {}, {}, (v) => "none", (v1, v2) => v2 === null, (v1, v2) => v2 !== null);
const BTypeNothing = new BType("Nothing", {}, {}, {}, (v) => "nothing", undefined, undefined);

const BTypeBool = new BType("Bool", {}, {}, {}, (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => !v1 && v2);

const BTypeNat = new BType("Nat", {}, {}, {}, (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);
const BTypeInt = new BType("Int", {}, {}, {}, (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);
const BTypeBigNat = new BType("BigNat", {}, {}, {}, (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);
const BTypeBigInt = new BType("BigInt", {}, {}, {}, (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);

const tirRegexMap = {
    /*TIR_REGEX_MAP_INIT*/
}; //string -> NFA


const tirTypeMap = {
    "None": BTypeNone,
    "Nothing": BTypeNothing,
    "Nat": BTypeNat,
    "Int": BTypeInt,
    "BigNat": BTypeBigNat,
    "BigInt": BTypeBigInt,
    /*TypeMap setup*/
};

const bsq_nonevalue = null;
const bsq_nothingvalue = undefined;

const bsq_environment = new Map(); //string -> {evtype: type, evvalue: value}
function bsq_envget(key, typekey, err) {
    if(!bsq_environment.has(key) || bsq_environment.get(key).evtype !== typekey) {
        throw err;
    }

    return bsq_environment.get(key).envvalue;
}

function bsq_envgetornone(key, typekey, err) {
    if(!bsq_environment.has(key)) {
        return bsq_nonevalue;
    }

    return bsq_envget(key, typekey, err);
}


export {
    BoxedValue,
    Unwind, createRuntimeError, checkOk,
    BType,
    BTypeNone, BTypeNothing,
    BTypeBool,
    BTypeNat, BTypeInt, BTypeBigNat, BTypeBigInt,
    tirRegexMap,
    tirTypeMap,

    bsq_nonevalue, bsq_nothingvalue,
    bsq_environment, bsq_envget, bsq_envgetornone
};

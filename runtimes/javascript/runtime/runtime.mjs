"use strict";

function BoxedValue(btype, bvalue) {
    this.btype = btype;
    this.btype = bvalue;
}

function Unwind(kind, msg) {
    this.kind = kind;
    this.msg = msg;
}

function checkOkAll(condarray, value) {
    const failc = cond.find((ce) => !ce[0]);
    if(failc !== undefined) {
        throw failc[1];
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

const TIRRegexMap = {
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

export {
    BoxedValue,
    Unwind, checkOk, checkOkAll,
    BType,
    BTypeNone, BTypeNothing,
    BTypeBool,
    BTypeNat, BTypeInt, BTypeBigNat, BTypeBigInt,
    TIRRegexMap
};

"use strict";

function BType(tkey, vtable, fdisplay, feq, fless) {
    this.tkey = tkey;
    this.vtable = vtable;
    this.fdisplay = fdisplay;
    this.feq = feq;
    this.fless = fless;
}

const BTypeNone = new BType("None", new Map(), (v) => "none", (v1, v2) => v2 === null, (v1, v2) => v2 !== null);
const BTypeNothing = new BType("Nothing", new Map(), (v) => "nothing", undefined, undefined);

const BTypeBool = new BType("Bool", new Map(), (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => !v1 && v2);

const BTypeNat = new BType("Nat", new Map(), (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);
const BTypeInt = new BType("Int", new Map(), (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);
const BTypeBigNat = new BType("BigNat", new Map(), (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);
const BTypeBigInt = new BType("BigInt", new Map(), (v) => `${v}`, (v1, v2) => v1 === v2, (v1, v2) => v1 < v2);

export {
    BType,
    BTypeNone, BTypeNothing,
    BTypeBool,
    BTypeNat, BTypeInt, BTypeBigNat, BTypeBigInt,
};

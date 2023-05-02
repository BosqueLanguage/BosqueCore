"use strict";

import * as assert from "assert";
import * as $Limits from "./limits.mjs";
import * as $CoreLibs from "./corelibs.mjs";
import * as $Runtime from "./runtime.mjs";
//--GENERATED_$usermodules--

//TODO: we need to validate a bit more aggressively in the primitives -- e.g. better errors with checks for like number string format, ascii strings are acsii, etc.

const ioMarshalMap = new Map();
ioMarshalMap.set("None", {parse: (jv) => jv !== null ? $Runtime.raiseRuntimeError(`expected None got ${jv}`) : null, emit: (nv) => null});
ioMarshalMap.set("Bool", {parse: (jv) => (jv === true || jv === false) ? jv : $Runtime.raiseRuntimeError(`expected Bool got ${jv}`), emit: (nv) => nv});
ioMarshalMap.set("Nat", {parse: (jv) => (typeof(jv) === "number") ? jv : $Runtime.raiseRuntimeError(`expected Nat got ${jv}`), emit: (nv) => nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("Int", {parse: (jv) => (typeof(jv) === "number") ? jv : $Runtime.raiseRuntimeError(`expected Int got ${jv}`), emit: (nv) => Number.MIN_SAFE_INTEGER <= nv && nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("BigNat", {parse: (jv) => (typeof(jv) === "number" || typeof(jv) === "string") ? BigInt(jv) : $Runtime.raiseRuntimeError(`expected BigNat got ${jv}`), emit: (nv) => nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("BigInt", {parse: (jv) => (typeof(jv) === "number" || typeof(jv) === "string") ? BigInt(jv) : $Runtime.raiseRuntimeError(`expected BigInt got ${jv}`), emit: (nv) => Number.MIN_SAFE_INTEGER <= nv && nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("Float", {parse: (jv) => jv, emit: (nv) => nv});
ioMarshalMap.set("Decimal", {parse: (jv) => new $Runtime.Decimal(jv), emit: (nv) => nv.toString()});
ioMarshalMap.set("Rational", {parse: (jv) => new $Runtime.Fraction(jv), emit: (nv) => nv.toFraction()});
ioMarshalMap.set("String", {parse: (jv) => typeof(jv) === "string" ? jv : $Runtime.raiseRuntimeError(`expected String got ${jv}`), emit: (nv) => nv});
ioMarshalMap.set("ASCIIString", {parse: (jv) => typeof(jv) === "string" ? jv :  $Runtime.raiseRuntimeError(`expected ASCIIString got ${jv}`), emit: (nv) => nv});
ioMarshalMap.set("DateTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("UTCDateTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("PlainDate", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("PlainTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("TickTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("LogicalTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("ISOTimeStamp", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("UUIDv4", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("UUIDv7", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("SHAContentHash", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("LatLongCoordinate", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("Nothing", {parse: (jv) => undefined, emit: (nv) => undefined});
//--GENERATED_$iomarshalsetup--

function tryParseConcept(jv) {
    $Runtime.raiseRuntimeErrorIf(!Array.isArray(jv) || jv.length !== 2, `${jv} is not a valid union representation`);
    $Runtime.raiseRuntimeErrorIf(typeof(jv[0]) !== "string" || ioMarshalMap.get(jv[0]) === undefined, `${jv} is not a valid union representation`);

    return $Runtime.UnionValue.create(jv[0], ioMarshalMap.get(jv[0]).parse(jv[1]));
}

function tryEmitConcept(nv) {
    return [nv.tkey, ioMarshalMap.get(nv.tkey).emit(nv.value)];
}

function tryParseUnion(jv) {
    $Runtime.raiseRuntimeErrorIf(!Array.isArray(jv) || jv.length !== 2, `${jv} is not a valid union representation`);
    $Runtime.raiseRuntimeErrorIf(typeof(jv[0]) !== "string" || ioMarshalMap.get(jv[0]) === undefined, `${jv} is not a valid union representation`);

    return $Runtime.UnionValue.create(jv[0], ioMarshalMap.get(jv[0]).parse(jv[1]));
}

function tryEmitUnion(nv) {
    return [nv.tkey, ioMarshalMap.get(nv.tkey).emit(nv.value)];
}

function checkIsObjectWithKeys(obj, keyarray) {
    if(obj === null || Array.isArray(obj) || typeof(obj) !== "object") {
        return false;
    }

    const ka = [...keyarray].sort();
    const keys = Object.keys(obj).sort();

    if(ka.length !== keys.length) {
        return false;
    }

    for(let i = 0; i < ka.length; ++i) {
        if(ka[i] !== keys[i]) {
            return false;
        }
    }
    return true;
}

function bsqMarshalParse(tt, jv) {
    return ioMarshalMap.get(tt).parse(jv);
}

function bsqMarshalEmit(tt, nv) {
    return ioMarshalMap.get(tt).emit(nv);
}

function cmdunescape(str) {
    return str.replace(/&amp;|&lt;|&gt;|&#39;|&quot;/g, 
    tag => ({
        '&amp;': '&',
        '&lt;': '<',
        '&gt;': '>',
        '&#39;': "'",
        '&quot;': '"'
      }[tag]));
}

export {
    bsqMarshalParse, bsqMarshalEmit, cmdunescape
};

"use strict";

import * as assert from "assert";
import * as $CoreLibs from "./corelibs.mjs";
import * as $Runtime from "./runtime.mjs";
//--GENERATED_$usermodules--

const ioMarshalMap = new Map();
ioMarshalMap.set("None", {parse: (jv) => null, emit: (nv) => null});
ioMarshalMap.set("Bool", {parse: (jv) => jv === "true", emit: (nv) => nv});
ioMarshalMap.set("Nat", {parse: (jv) => BigInt(jv), emit: (nv) => nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("Int", {parse: (jv) => BigInt(jv), emit: (nv) => Number.MIN_SAFE_INTEGER <= nv && nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("BigNat", {parse: (jv) => BigInt(jv), emit: (nv) => nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("BigInt", {parse: (jv) => BigInt(jv), emit: (nv) => Number.MIN_SAFE_INTEGER <= nv && nv <= Number.MAX_SAFE_INTEGER ? Number(nv) : `"${nv.toString()}"`});
ioMarshalMap.set("Rational", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("Float", {parse: (jv) => jv, emit: (nv) => nv});
ioMarshalMap.set("Rational", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("String", {parse: (jv) => jv, emit: (nv) => nv});
ioMarshalMap.set("DateTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("UTCDateTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("PlainDate", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("PlainTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("TickTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("LogicalTime", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("ISOTimeStamp", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("UUID4", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("UUID7", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("SHAContentHash", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("LatLongCoordinate", {parse: (jv) => assert(false), emit: (nv) => assert(false)});
ioMarshalMap.set("Nothing", {parse: (jv) => undefined, emit: (nv) => undefined});
//--GENERATED_$iomarshalsetup--

function tryParseUnion(jv) {
    $Runtime.raiseRuntimeErrorIf(!Array.isArray(jv) || jv.length !== 2, `${jv} is not a valid union representation`);
    $Runtime.raiseRuntimeErrorIf(typeof(jv[0]) !== "string" || ioMarshalMap.get(jv[0]) === undefined, `${jv} is not a valid union representation`);

    return new $Runtime.UnionValue(jv[0], ioMarshalMap.get(jv[0]).parse(jv[1]));
}

function tryEmitUnion(nv) {
    return [nv.tkey, ioMarshalMap.get(jv[nv.tkey]).emit(nv.value)];
}

function bsqMarshalParse(tt, jv) {
    return ioMarshalMap.get(tt).parse(jv);
}

function bsqMarshalEmit(tt, nv) {
    return ioMarshalMap.get(tt).emit(nv);
}

export {
    bsqMarshalParse, bsqMarshalEmit,
};

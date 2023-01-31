"use strict";

import * as assert from "assert";
import { List as IList, Map as IMap } from "immutable";

function UnionValue(tkey, value) {
    this.tkey = tkey;
    this.value = value;
}

const subtypeMap = new Map();
//--GENERATED_$subtypesetup--

const vtablemap = new Map();
//--GENERATED_$vtablesetup--

const ioMarshalMap = new Map();
ioMarshalMap.set("None", {parse: (jv) => undefined, emit: (nv) => undefined});
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
//--GENERATED_$iomarshalsetup--

const lambdas = new Map();
//--GENERATED_$lambdas--

function isSubtype(tkey, ofkey) {
    if(tkey === ofkey) {
        return true;
    }
    else {
        assert(subtypeMap.has(ofkey), "Internal error -- missing subtype entry");
        return subtypeMap.get(ofkey).includes(tkey);
    }
}

function bsqMarshalParse(tt, jv) {
    return ioMarshalMap.get(tt).parse(jv);
}

function bsqMarshalEmit(tt, nv) {
    return ioMarshalMap.get(tt).emit(nv);
}

const FIXED_NUMBER_MAX = 9223372036854775808n; 
const FIXED_NUMBER_MIN = -9223372036854775808n; 

function Unwind(kind, msg) {
    this.kind = kind;
    this.msg = msg;
}

function raiseRuntimeError(msg) {
    throw new Unwind("error", msg);
}

function raiseRuntimeErrorIf(cond, msg) {
    if(cond) {
        throw new Unwind("error", msg);
    }
}

function raiseUserAssert(msg) {
    throw new Unwind("assert", msg);
}

function raiseUserAssertIf(cond, msg) {
    if(cond) {
        throw new Unwind("assert", msg);
    }
}

function setScratchValue(scratch, sidx, value) {
    scratch[sidx] = value;
    return 0;
}

function safeMath(val, lb, ub) {
    raiseRuntimeErrorIf(val < lb || ub < val, `bounded arithmetic op overflowed`);
    return val;
}

function safeMathUnderflow(val, zero) {
    raiseRuntimeErrorIf(val < zero, `arithmetic op underflow`);
    return val;
}

function safeMathDiv(op, chk, v1, v2) {
    raiseRuntimeErrorIf(!chk(v2), `division by 0`);
    return val;
}

function BSQEnvironment(env, ...args) {
    this.parent = env;
    this.args = new Map();
    for(let i = 0; i < args.length; ++i) {
        this.args.set(args[i][0], args[i][1]);
    }
}

BSQEnvironment.push = function(env) {
    return new BSQEnvironment(env);
};

BSQEnvironment.pop = function(env) {
    return env.parent;
}

BSQEnvironment.has = function(env, key) {
    if(env.args.has(key)) {
        const vv = env.args.get(key);
        return vv !== undefined;
    }

    return env.parent !== undefined && BSQEnvironment.has(env.parent, key);
};

BSQEnvironment.get = function(env, key, oftype) {
    if(env.args.has(key)) {
        const vv = env.args.get(key);
        raiseRuntimeErrorIf(vv === undefined, `key ${key} was not found in environment`); //tombstone

        raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
        return vv.value;
    }

    raiseRuntimeErrorIf(env.parent === undefined, `key ${key} was not found in environment`);
    return BSQEnvironment.get(env.parent, key, oftype);
};

BSQEnvironment.getOrNoneUV = function(env, key, oftype) {
    if(env.args.has(key)) {
        const vv = env.args.get(key);
        if(vv === undefined) {
           return new UnionValue("BSQNone", undefined); //tombstone
        }

        raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
        return new UnionValue(vv.tkey, vv.value);
    }

    if(env.parent === undefined) {
        return new UnionValue("BSQNone", undefined);
    }
    else {
        return BSQEnvironment.getOrNoneUV(env.parent, key, oftype);
    }
};

BSQEnvironment.getOrNoneDV = function(env, key, oftype) {
    if(env.args.has(key)) {
        const vv = env.args.get(key);
        if(vv === undefined) {
           return new UnionValue("BSQNone", undefined); //tombstone
        }

        raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
        return vv.value;
    }

    if(env.parent === undefined) {
        return new UnionValue("BSQNone", undefined);
    }
    else {
        return BSQEnvironment.get(env.parent, key, oftype);
    }
};

BSQEnvironment.set = function(env, key, val, oftype) {
    env.args.set(key, {tkey: oftype, value: val});
};

BSQEnvironment.clear = function(env, key) {
    raiseRuntimeErrorIf(!BSQEnvironment.has(env, key), `key ${key} not defined in environment`);
    env.args.set(key, undefined);
};

//
//TODO: logging needs to be configured on a per task level -- i.e. should be member vars on a task
//

let loglevel = "info";
let logprefix = [];

function setloglevel(level) {
    loglevel = level;
}

function checkloglevel(level) {
    return level === "fatal" || level === "error" || level === "warn" || level === "info";
}

function log(level, tag, fmt, ...args) {
    const msg = fmt + " -- " + args.map((arg) => JSON.stringify(arg)).join(" ");
    if(logprefix.length === 0) {
        console.log(JSON.stringify(
            {
                tag: tag,
                msg: msg
            }
        ));
    }
    else {
        console.log(JSON.stringify(
            {
                tag: tag,
                prefix: logprefix.map((pp) => pp.smsg),
                msg: msg
            }
        ));
    }

    if(level === "fatal") {
        raiseUserAssert("log at fatal level -- " + msg);
    }
}

function pushlogprefix(fmt, ...args) {
    const smsg = fmt + " -- " + args.map((arg) => JSON.stringify(arg)).join(" ");
    logprefix.push({fmt: fmt, args: args, smsg: smsg});
}

function poplogprefix() {
    logprefix.pop();
}

export {
    UnionValue, isSubtype,
    vtablemap,
    lambdas,
    bsqMarshalParse, bsqMarshalEmit,
    FIXED_NUMBER_MAX, FIXED_NUMBER_MIN,
    Unwind, raiseRuntimeError, raiseRuntimeErrorIf, raiseUserAssert, raiseUserAssertIf,
    setScratchValue, 
    safeMath, safeMathDiv, safeMathUnderflow,
    BSQEnvironment,
    setloglevel, checkloglevel, log, pushlogprefix, poplogprefix
};

"use strict";

import * as assert from "assert";

import { JS, NFA, Words } from "refa";
import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

function UnionValue(tkey, value) {
    this.tkey = tkey;
    this.value = value;
}

const subtypeMap = new Map();
//--GENERATED_$subtypesetup--

const vtablemap = new Map();
//--GENERATED_$vtablesetup--

const lambdas = new Map();

function isSubtype(tkey, ofkey) {
    if(tkey === ofkey) {
        return true;
    }
    else {
        const chkinfo = subtypeMap.get(ofkey);
        if(chkinfo.direct.has(tkey)) {
            return true;
        }
        else {
            return chkinfo.indirect.some((iid) => isSubtype(tkey, iid));
        }
    }
}

//2^63 - 1 ## this way (1) negation and conversion MInt<->MNat is always safe (2) we can steal the top bit for tagging on Int/Nat later
const FIXED_NUMBER_MAX = 9223372036854775807n;
const FIXED_NUMBER_MIN = -9223372036854775807n; 

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
    return op(v1, v2);
}

function BSQEnvironment(env, ...args) {
    this.parent = env;
    this.args = new Map();
    for(let i = 0; i < args.length; ++i) {
        this.args.set(args[i][0], args[i][1]);
    }
}

function acceptsString(re, str) {
    const jsre = RegExp(re);

    const { expression, maxCharacter } = JS.Parser.fromLiteral(jsre).parse();
    const nfa = NFA.fromRegex(expression, { maxCharacter });

    return nfa.test(Words.fromStringToUnicode(str));
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
    return level === "fatal" || level === "error" || level === "warn" || level === "info"; //we are stuck at "info" so "debug" is off
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
    FIXED_NUMBER_MAX, FIXED_NUMBER_MIN,
    Unwind, raiseRuntimeError, raiseRuntimeErrorIf, raiseUserAssert, raiseUserAssertIf,
    setScratchValue, 
    safeMath, safeMathDiv, safeMathUnderflow,
    acceptsString,
    BSQEnvironment,
    setloglevel, checkloglevel, log, pushlogprefix, poplogprefix,
    Decimal, Fraction
};

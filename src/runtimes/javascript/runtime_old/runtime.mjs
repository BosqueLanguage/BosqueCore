"use strict";

import { JS, NFA, Words } from "refa";
import {Decimal} from "decimal.js";
import Fraction from "fraction.js";


const subtypeMap = new Map();
//--GENERATED_$subtypesetup--

const vtablemap = new Map();
//--GENERATED_$vtablesetup--

const invmap = new Map();
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

function setScratchValue(scratch, sidx, value) {
    scratch[sidx] = value;
    return 0;
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
           return UnionValue.create("BSQNone", undefined); //tombstone
        }

        raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
        return UnionValue.create(vv.tkey, vv.value);
    }

    if(env.parent === undefined) {
        return UnionValue.create("BSQNone", undefined);
    }
    else {
        return BSQEnvironment.getOrNoneUV(env.parent, key, oftype);
    }
};

BSQEnvironment.getOrNoneDV = function(env, key, oftype) {
    if(env.args.has(key)) {
        const vv = env.args.get(key);
        if(vv === undefined) {
           return UnionValue.create("BSQNone", undefined); //tombstone
        }

        raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
        return vv.value;
    }

    if(env.parent === undefined) {
        return UnionValue.create("BSQNone", undefined);
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
    vtablemap, invmap,
    lambdas,
    
    setScratchValue, 
    
    acceptsString,
    BSQEnvironment,
    setloglevel, checkloglevel, log, pushlogprefix, poplogprefix,
    Decimal, Fraction
};

"use strict";

import * as assert from "assert";

function UnionValue(tkey, value) {
    this.tkey = tkey;
    this.value = value;
}

const unionReprTypes = new Set();
const subtypeMap = new Map();

function isUnionReprType(tkey) {
    return unionReprTypes.has(tkey);
}

function isSubtype(tkey, ofkey) {
    if(tkey === ofkey) {
        return true;
    }
    else {
        assert(subtypeMap.has(ofkey), "Internal error -- missing subtype entry");
        return subtypeMap.get(ofkey).includes(tkey);
    }
}

function Unwind(kind, msg) {
    this.kind = kind;
    this.msg = msg;
}

function createRuntimeError(msg) {
    return Unwind("error", msg);
}

function createRuntimeErrorIf(cond, msg) {
    if(cond) {
        return Unwind("error", msg);
    }
}

function BSQEnvironment(env, ...args) {
    this.parent = env;
    this.args = new Map();
    for(let i = 0; i < args.length; ++i) {
        this.args.set(args[i][0], args[1]);
    }
}

BSQEnvironment.get = function(env, key, oftype) {
    if(env.args.has(key)) {
        const vv = env.args.get(key);
        createRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);

        return vv.value;
    }

    createRuntimeErrorIf(env.parent === undefined, `key ${key} was not found in environment`);
    return BSQEnvironment.get(env.parent, key, oftype);
};

BSQEnvironment.getOrNone = function(env, key, oftype) {
    if(env.args.has(key)) {
        const vv = env.args.get(key);
        createRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);

        return isUnionReprType(vv.tkey) ? vv.value : new UnionValue(vv.tkey, vv.value);
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
    this.createRuntimeErrorIf(!env.args.has(key), `key ${key} not defined in (local) environment`);
    env.args.delete(key);
};

export {
    UnionValue, isUnionReprType, isSubtype,
    Unwind, createRuntimeError, createRuntimeErrorIf,
    BSQEnvironment
};

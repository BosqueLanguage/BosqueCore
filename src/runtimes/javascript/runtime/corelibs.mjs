"use strict";

import * as assert from "assert";
import { List as IList, Map as IMap } from "immutable";
import { raiseRuntimeError } from "./runtime.mjs";

const $KeyEqualOps = new Map();
$KeyEqualOps.set("Nothing", (a, b) => (a === undefined && b === undefined)); //not a keytype but comparable with ===
$KeyEqualOps.set("None", (a, b) => (a === null && b === null));
$KeyEqualOps.set("Bool", (a, b) => (a === b));
$KeyEqualOps.set("Nat", (a, b) => (a === b));
$KeyEqualOps.set("Int", (a, b) => (a === b));
$KeyEqualOps.set("BigNat", (a, b) => (a === b));
$KeyEqualOps.set("BigInt", (a, b) => (a === b));
$KeyEqualOps.set("String", (a, b) => (a === b));
$KeyEqualOps.set("UTCDateTime", (a, b) => assert(false));
$KeyEqualOps.set("PlainDate", (a, b) => assert(false));
$KeyEqualOps.set("PlainTime", (a, b) => assert(false));
$KeyEqualOps.set("TickTime", (a, b) => assert(false));
$KeyEqualOps.set("LogicalTime", (a, b) => assert(false));
$KeyEqualOps.set("ISOTimeStamp", (a, b) => assert(false));
$KeyEqualOps.set("UUIDv4", (a, b) => assert(false));
$KeyEqualOps.set("UUIDv7", (a, b) => assert(false));
$KeyEqualOps.set("SHAContentHash", (a, b) => assert(false));
//--GENERATED_$KeyEqualOps--

const $KeyLessOps = new Map();
$KeyLessOps.set("None", (a, b) => false);
$KeyLessOps.set("Bool", (a, b) => (!a && b));
$KeyLessOps.set("Nat", (a, b) => (a < b));
$KeyLessOps.set("Int", (a, b) => (a < b));
$KeyLessOps.set("BigNat", (a, b) => (a < b));
$KeyLessOps.set("BigInt", (a, b) => (a < b));
$KeyLessOps.set("String", (a, b) => (a < b));
$KeyLessOps.set("UTCDateTime", (a, b) => assert(false));
$KeyLessOps.set("PlainDate", (a, b) => assert(false));
$KeyLessOps.set("PlainTime", (a, b) => assert(false));
$KeyLessOps.set("TickTime", (a, b) => assert(false));
$KeyLessOps.set("LogicalTime", (a, b) => assert(false));
$KeyLessOps.set("ISOTimeStamp", (a, b) => assert(false));
$KeyLessOps.set("UUIDv4", (a, b) => assert(false));
$KeyLessOps.set("UUIDv7", (a, b) => assert(false));
$KeyLessOps.set("SHAContentHash", (a, b) => assert(false));
//--GENERATED_$KeyLessOps--

function $KeyEqualMixed(uval, gval, oftype) {
    if(gval.tkey !== oftype) {
        return false;
    }

    return ($KeyEqualOps.get(oftype))(uval, gval.value);
}

function $KeyEqualGeneral(lval, rval) {
    if(lval.tkey !== rval.tkey) {
        return false;
    }

    return ($KeyEqualOps.get(lval.tkey))(lval.value, rval.value);
}

function $KeyLessGeneral(lval, rval) {
    if(lval.tkey !== rval.tkey) {
        return false;
    }

    return ($KeyLessOps.get(lval.tkey))(lval.value, rval.value);
}

function $NumericOps() {
}

function $StringOps() {
}

function $DateOps() {
}

function $ListOps() {
}
$ListOps.create = function(...args) {
    return IList(args);
}

function $MapOps() {
}
$MapOps.create = function(tkey, ...args) {
    const minit = IMap();
    const kcmp = $KeyEqualOps.get(tkey);
    const mres = minit.withMutations(map => {
        for(let i = 0; i < args.length; ++i) {
            //TODO: I think Bosque key equality and immutable.js equality are the same so -- just go for it here
            if(map.has(args[i][0])) {
                raiseRuntimeError("duplicate keys in Map construction");
            }
            
            map = map.set(args[i][0], args[i][1]);
        }
    });

    return mres;
};


export {
    $KeyEqualOps, $KeyLessOps,
    $KeyEqualMixed, $KeyEqualGeneral, $KeyLessGeneral,
    $NumericOps, $StringOps, $DateOps, $ListOps, $MapOps
};

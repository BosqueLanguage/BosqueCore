"use strict";

const { IList, IMap } = require('immutable')

const $KeyEqualOps = new Map();
$KeyEqualOps.set("None", (a, b) => (a === undefined && b === undefined));
$KeyEqualOps.set("Bool", (a, b) => (a === b));
//--GENERATED_$KeyEqualOps--

const $KeyLessOps = new Map();
$KeyLessOps.set("None", (a, b) => false);
$KeyLessOps.set("Bool", (a, b) => (!a && b));
//--GENERATED_$KeyLessOps--

function $KeyEqualMixed(uval, gval, oftype) {
    if(gval.tkey !== oftype) {
        return false;
    }

    return ($KeyEqualOps.get(oftype))(uval, garg.value);
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
$MapOps.create = function(...args) {
    const minit = IMap();
    const mres = minit.withMutations(map => {
        for(let i = 0; i < args.length; ++i) {
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

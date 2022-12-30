"use strict";

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

export {
    $KeyEqualOps, $KeyLessOps,
    $KeyEqualMixed, $KeyEqualGeneral, $KeyLessGeneral
};

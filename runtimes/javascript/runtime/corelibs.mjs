"use strict";

const $KeyEqualOps = new Map();
$KeyEqualOps.set("None", (a, b) => (a === undefined && b === undefined));
$KeyEqualOps.set("Bool", (a, b) => (a === b));
//--GENERATED_$KeyEqualOps--

const $KeyLessOps = new Map();
$KeyLessOps.set("None", (a, b) => false);
$KeyLessOps.set("Bool", (a, b) => (!a && b));
//--GENERATED_$KeyLessOps--

export {
    $KeyEqualOps, $KeyLessOps
};

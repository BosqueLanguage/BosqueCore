"use strict";

import * as assert from "assert";
import { List as IList, Map as IMap } from "immutable";
import * as $Runtime from "./runtime.mjs";


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
    const mres = minit.withMutations(map => {
        for(let i = 0; i < args.length; ++i) {
            //TODO: I think Bosque key equality and immutable.js equality are the same so -- just go for it here
            if(map.has(args[i][0])) {
                $Runtime.raiseRuntimeError("duplicate keys in Map construction");
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

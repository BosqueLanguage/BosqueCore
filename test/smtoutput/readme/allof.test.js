"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

const allpositive = 'function allPositive(...args: List<Int>): Bool { return args.allOf(pred(x) => x >= 0i); }';

describe ("SMT allof", () => {
    it("should exec allof", function () {
        runishMainCodeUnsat(`${allpositive} public function main(): Bool { return allPositive(1i, 3i, 4i); }`, "(assert (not Main@main))"); 
        runishMainCodeUnsat(`${allpositive} public function main(): Bool { return allPositive(); }`, "(assert (not Main@main))");
        runishMainCodeUnsat(`${allpositive} public function main(): Bool { return allPositive(1i, 3i, -4i); }`, "(assert Main@main)");
    });
});

"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT README -- sub2 exec", () => {
    it("should smt exec sub2", function () {
        runishMainCodeUnsat('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(4i, 2i); }', "(assert (not (= 2 Main@main)))"); 
        runishMainCodeUnsat('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(y=2i, x=3i); }', "(assert (not (= 1 Main@main)))");
    });
});

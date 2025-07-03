"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- elist return", () => {
    it("should smt exec elist returns", function () {
        runishMainCodeUnsat('function foo(): (|Int, Bool|) { return (|2i, false|); } public function main(): Int { return foo().0; }', "(assert (not (= 2 Main@main)))");
        runishMainCodeUnsat('function foo(): (|Int, Bool|) { return 2i, false; } public function main(): Int { return foo().0; }', "(assert (not (= 2 Main@main)))");
    });

    it("should smt exec elist returns w/ convert", function () {
        runishMainCodeUnsat('function foo(): (|Option<Int>, Bool|) { return (|some(2i), false|); } public function main(): Int { return foo().0@some; }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('function foo(): (|Option<Int>, Bool|) { return some(2i), false; } public function main(): Int { return foo().0@some; }', "(assert (not (= (@Result-ok 2) Main@main)))");
    });
});

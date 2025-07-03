"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- type decl of bool", () => {
    it("should smt exec bool type decl", function () {
        runishMainCodeUnsat("type Flag = Bool; public function main(): Bool { let e = true<Flag>; return e.value; }", "(assert (not Main@main))"); 
    });
});

describe ("SMT -- type decl of number", () => {
    it("should smt exec numeric type decls", function () {
        runishMainCodeUnsat('type NVal = Int; public function main(): Int { let e = -2i<NVal>; return e.value; }', "(assert (not (= -2 Main@main)))");
    });
});


"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- multi declare-assign only", () => {
    it("should smt exec multi declare-assign", function () {
        runishMainCodeUnsat("public function main(): Int { var x: Int, y: Bool = 1i, true; return x; }", "(assert (not (= 1 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { var x: Int, j: Bool = 1i, true; return x; }", "(assert (not (= 1 Main@main)))");
        
        runishMainCodeUnsat("public function main(): Int { var x, y = 1i, true; return x; }", "(assert (not (= 1 Main@main)))");

        runishMainCodeUnsat("public function main(): Int { var x: Int, k, z: Int = 1i, true, 0i; return x; }", "(assert (not (= 1 Main@main)))");
    });

    it("should smt multi declare-assign from elist", function () {
        runishMainCodeUnsat("public function main(): Int { var x: Int, y: Bool = (|1i, true|); return x; }", "(assert (not (= 1 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { var x: Int, _: Bool = (|1i, true|); return x; }", "(assert (not (= 1 Main@main)))");
        
        runishMainCodeUnsat("public function main(): Int { var x, y = (|1i, true|); return x; }", "(assert (not (= 1 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { var x, _ = (|1i, true|); return x; }", "(assert (not (= 1 Main@main)))");

        runishMainCodeUnsat("public function main(): Int { var x, _, _ = (|1i, true, false|); return x; }", "(assert (not (= 1 Main@main)))");
    });
});

describe ("SMT -- multi assign", () => {
    it("should smt exec multi assign", function () {
        runishMainCodeUnsat("public function main(): Int { var x: Int = 1i; var y: Bool; x, y = 2i, false; return x; }", "(assert (not (= 2 Main@main)))");

        runishMainCodeUnsat("public function main(): Int { var x: Int = 1i; x, _ = (|2i, false|); return x; }", "(assert (not (= 2 Main@main)))");
    });
});
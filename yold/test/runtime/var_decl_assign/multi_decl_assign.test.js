"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- multi declare-assign only", () => {
    it("should exec multi declare-assign", function () {
        runMainCode("public function main(): Int { var x: Int, y: Bool = 1i, true; return x; }", "1i");
        runMainCode("public function main(): Int { var x: Int, j: Bool = 1i, true; return x; }", "1i");
        
        runMainCode("public function main(): Int { var x, y = 1i, true; return x; }", "1i");

        runMainCode("public function main(): Int { var x: Int, k, z: Int = 1i, true, 0i; return x; }", "1i");
    });

    it("should exec multi declare-assign from elist", function () {
        runMainCode("public function main(): Int { var x: Int, y: Bool = (|1i, true|); return x; }", "1i");
        runMainCode("public function main(): Int { var x: Int, _: Bool = (|1i, true|); return x; }", "1i");
        
        runMainCode("public function main(): Int { var x, y = (|1i, true|); return x; }", "1i");
        runMainCode("public function main(): Int { var x, _ = (|1i, true|); return x; }", "1i");

        runMainCode("public function main(): Int { var x, _, _ = (|1i, true, false|); return x; }", "1i");
    });
});

describe ("Exec -- multi assign", () => {
    it("should exec multi assign", function () {
        runMainCode("public function main(): Int { var x: Int = 1i; var y: Bool; x, y = 2i, false; return x; }", "2i");

        runMainCode("public function main(): Int { var x: Int = 1i; x, _ = (|2i, false|); return x; }", "2i");
    });
});
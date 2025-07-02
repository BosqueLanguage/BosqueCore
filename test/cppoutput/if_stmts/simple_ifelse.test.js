"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Simple if-elif-else statements", () => {
    it("should exec simple ifelse", function () {
        runMainCode("public function main(): Int { if(1n != 2n) { return 2i; } else { return 3i; } }", "2_i")
    });
    it("should exec simple ifelifelse", function () {
        runMainCode("public function main(): Int { if(1n == 2n) { return 2i; } elif(1n == 3n) { return 1i; } elif(2i == 2i) { return 4i; } else { return 3i; } }", "4_i")
    });
    it("should exec itest ifelses", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } else { return 1i; } }", "3_i");
        runMainCode("public function main(): Int { let x: Option<Int> = none; if(x)some { return 3i; } else { return 1i; } }", "1_i");
    });
    it("should exec binder itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $x; } else { return 1i; } }", "3i");
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if($y = x)@some { return $y; } else { return 1i; } }", "3i");

        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@none { return 1i; } else { return $x; } }", "3i");
        runMainCode("public function main(): Int { let x: Option<Int> = none; if(x)@none { return 1i; } else { return $x; } }", "1i");
    });

    it("should exec binder & reflow itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@@!some { return 0i; } else { ; } return x; }", "3i");
    });
});
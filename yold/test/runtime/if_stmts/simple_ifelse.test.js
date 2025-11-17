"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- IfElse Statement", () => {
    it("should exec simple ifs", function () {
        runMainCode("public function main(): Int { if(true) { return 3i; } else { return 1i; } }", "3i");
        runMainCode("public function main(): Int { if(false) { return 3i; } else { return 1i; } }", "1i");

        runMainCode("public function main(): Int { if(false) { return 3i; } else { ; } return 1i; }", "1i");
    });

    it("should exec itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } else { return 1i; } }", "3i");
        runMainCode("public function main(): Int { let x: Option<Int> = none; if(x)some { return 3i; } else { return 1i; } }", "1i");
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

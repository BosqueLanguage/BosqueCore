"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- If Statement", () => {
    it("should exec simple ifs", function () {
        runMainCode("public function main(): Int { if(true) { return 3i; } return 1i; }", [3n, "Int"]);
        runMainCode("public function main(): Int { if(false) { return 3i; } return 1i; }", [1n, "Int"]);
    });

    it("should exec itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } return 1i; }", [3n, "Int"]);
        runMainCode("public function main(): Int { let x: Option<Int> = none; if(x)some { return 3i; } return 1i; }", [1n, "Int"]);
    });

    it("should exec binder itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $x; } return 1i; }", [3n, "Int"]);
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if($y = x)@some { return $y; } return 1i; }", [3n, "Int"]);
    });

    it("should exec binder & reflow itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@@!some { return 0i; } return x; }", [3n, "Int"]);
        runMainCode("public function main(): Int { let x: Option<Int> = none; if(x)@@!some { return 0i; } return x; }", [0n, "Int"]);
    });
});


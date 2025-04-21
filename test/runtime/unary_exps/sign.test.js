"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple numeric sign", () => {
    it("should exec (simplify) simple sign", function () {
        runMainCode("public function main(): Int { return -(3i); }", "-3i");
        runMainCode("public function main(): Nat { return +(5n); }", "5n");
    });

    it("should exec simple sign", function () {
        runMainCode("public function main(): Int { let x = 3i; return -x; }", "-3i");
        runMainCode("public function main(): Nat { let x = 5n; return +x; }", "5n");
    });
});

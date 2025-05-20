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
});
"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- If Statement", () => {
    it("should exec simple ifs", function () {
        runMainCode("public function main(): Int { if(true) { return 3i; } return 1i; }", "3_i");
        runMainCode("public function main(): Int { if(false) { return 3i; } return 1i; }", "1_i");
    });
});
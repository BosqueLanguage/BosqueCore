"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Simple if-expression", () => {
    it("should exec simple", function () {
        runMainCode("public function main(): Int { return if(1n != 2n) then 2i else 3i; }", "2_i");
        runMainCode("public function main(): Int { return if(2n != 2n) then 2i else 3i; }", "3_i");
    });
});

//
// TODO: Add support for ITests so we can run some ITest + ifexp tests
//
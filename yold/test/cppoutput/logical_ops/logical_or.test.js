"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- logical or", () => {
    it("should exec simple or", function () {
        runMainCode("public function main(): Bool { return true || false; }", "true");
        runMainCode("public function main(): Bool { return false || false; }", "false");
    });

    it("should exec sc or", function () {
        runMainCode("public function main(): Bool { return true || (1i // 0i) == 1i; }", "true");
    });
});
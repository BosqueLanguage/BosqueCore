"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- logical and", () => {
    it("should exec simple and", function () {
        runMainCode("public function main(): Bool { return true && false; }", "false");
        runMainCode("public function main(): Bool { return true && true; }", "true");
    });

    it("should exec sc and", function () {
        runMainCode("public function main(): Bool { return false && (1i // 0i) == 1i; }", "false");
    });
});
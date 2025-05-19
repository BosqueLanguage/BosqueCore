"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe("CPP Emit Evaluate -- Bool", () => {
    it("should exec simple boolean", function () {
        runMainCode("public function main(): Bool { return true; }", "true");
        runMainCode("public function main(): Bool { return false; }", "false");
    });
});
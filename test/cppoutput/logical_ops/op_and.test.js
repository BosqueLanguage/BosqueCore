"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- op and", () => {
    it("should exec simple and", function () {
        runMainCode("public function main(): Bool { return /\\(true); }", "true");
        runMainCode("public function main(): Bool { return /\\(true, false); }", "false");
        runMainCode("public function main(): Bool { return /\\(true, false, true); }", "false");
    });
});
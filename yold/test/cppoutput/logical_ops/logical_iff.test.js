"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- logical iff", () => {
    it("should exec simple iff", function () {
        runMainCode("public function main(): Bool { return true <==> false; }", "false");
        runMainCode("public function main(): Bool { return false <==> false; }", "true");
    });
});
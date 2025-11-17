"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- logical iff", () => {
    it("should exec simple iff", function () {
        runMainCode("public function main(): Bool { return true <==> false; }", "false");
        runMainCode("public function main(): Bool { return false <==> false; }", "true");
    });
});

"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- logical iff", () => {
    it("should exec simple iff", function () {
        runMainCode("public function main(): Bool { return true <==> false; }", [false, "Bool"]);
        runMainCode("public function main(): Bool { return false <==> false; }", [true, "Bool"]);
    });

    it("should exec NOT sc iff", function () {
        runMainCodeError("public function main(): Bool { return true <==> (1i // 0i) == 1i; }", "Error -- division by zero @ test.bsq:3");
    });
});

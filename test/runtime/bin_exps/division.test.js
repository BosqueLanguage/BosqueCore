"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple division", () => {
    it("should exec simple nats", function () {
        runMainCode("public function main(): Nat { return 1n // 1n; }", [1n, "Nat"]);
        runMainCode("public function main(): Int { return +2i // -2i; }", [-1n, "Int"]);
    });

    it("should fail div 0", function () {
        runMainCodeError("public function main(): Int { return 2i // 0i; }", "Error -- division by zero @ test.bsq:3");
    });
});

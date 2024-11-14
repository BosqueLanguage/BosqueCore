"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple subtraction", () => {
    it("should check simple nats", function () {
        runMainCode("public function main(): Nat { return 1n - 1n; }", [0n, "Nat"]);
        runMainCode("public function main(): Int { return 2i - -2i; }", [4n, "Int"]);
    });

    it("should fail underflow", function () {
        runMainCodeError("public function main(): Nat { return 1n - 5n; }", "Error -- Overflow");
    });
});

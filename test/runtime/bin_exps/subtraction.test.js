"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple subtraction", () => {
    it("should check simple nats", function () {
        runMainCode("public function main(): Nat { return 1n - 1n; }", [0n, "Nat"]);
        runMainCode("public function main(): Int { return 2i - -2i; }", [4n, "Int"]);
    });

    /*
    it("should fail not same type", function () {
        checkTestExpError("0n - 5i", "Int", "Subtraction operator requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none - true", "Nat", "Binary operator requires a unique numeric type");
    });
    */
});

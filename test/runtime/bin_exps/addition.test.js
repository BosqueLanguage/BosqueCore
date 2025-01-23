"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- Simple addition", () => {
    it("should exec simple nats", function () {
        runMainCode("public function main(): Nat { return 0n + 1n; }", "1n");
        runMainCode("public function main(): Int { return +2i + -2i; }", "0i");
    });
});

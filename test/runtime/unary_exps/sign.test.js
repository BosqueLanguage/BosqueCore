"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple numeric sign", () => {
    it("should check simple not", function () {
        runMainCode("public function main(): Int { return -(3i); }", "-3i");
        runMainCode("public function main(): Nat { return +(5n); }", "5n");
    });
});

"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- basic <", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n < 1n; }", "true");
        runMainCode("public function main(): Bool { return +2i < -2i; }", "false");

        runMainCode("public function main(): Bool { return 1n < 1n; }", "false");
    });
});

describe ("Exec -- basic <=", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n <= 1n; }", "true");
        runMainCode("public function main(): Bool { return +2i <= -2i; }", "false");

        runMainCode("public function main(): Bool { return 1n <= 1n; }", "true");
    });
});

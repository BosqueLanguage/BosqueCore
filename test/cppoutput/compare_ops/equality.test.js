"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe("CPP Emit Evalutate -- basic equals", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n == 1n; }", "false");
        runMainCode("public function main(): Bool { return +2i == 2i; }", "true");
    })
});

describe("CPP Emit Evalutate -- basic !equals", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n != 1n; }", "true");
        runMainCode("public function main(): Bool { return +2i != 2i; }", "false");
    })
});
"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple subtraction", () => {
    it("should emit simple ops", function () {
        runTestSet("public function main(x: Nat): Nat { return 1n - x; }", [['1n', '0n'], ['0n', '1n']], ['5n']);
        runTestSet("public function main(x: Int): Int { return 2i - x; }", [['2i', '0i'], ['-1i', '3i'], ['0i', '2i']], []);
    });
});
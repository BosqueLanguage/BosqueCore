"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple multiplication", () => {
    it("should exec simple ops", function () {
        runTestSet("public function main(x: Nat): Nat { return 2n * x; }", [['0n', '0n'], ['1n', '2n']], ['4611686018427387900n']);
        runTestSet("public function main(x: Int): Int { return -1i * x; }", [['0i', '0i'], ['1i', '-1i'], ['-3i', '3i'], ['4611686018427387903i', '-4611686018427387903i']], []);
    });
});

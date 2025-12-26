"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple addition", () => {
    it("should exec simple ops", function () {
        runTestSet("public function main(x: Nat): Nat { return 5n + x; }", [['0n', '5n'], ['1n', '6n']], ['4611686018427387900n']);
        runTestSet("public function main(x: Int): Int { return x + 2i; }", [['0i', '2i'], ['-1i', '1i'], ['3i', '5i'], ['-4611686018427387903i', '-4611686018427387901i']], ['4611686018427387903i']);
    });
});

"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Int operation trees", () => {
    it("should exec simple pm", function () {
        runTestSet("public function main(x: Int): Int { return x + 1i - 4i; }", [['0i', '-3i'], ['4i', '1i']], []);
        runTestSet("public function main(x: Nat): Nat { return (x + 1n) - 2n; }", [['2n', '1n'], ['1n', '0n']], ['0n']);
    });

    it("should exec precedence pm", function () {
        runTestSet("public function main(x: Int): Int { return (x + 1i) * -4i; }", [['0i', '-4i'], ['-1i', '0i']], ['4611686018427387900i']);
        runTestSet("public function main(x: Int): Int { return x + (1i * -4i); }", [['0i', '-4i'], ['4i', '0i']], ['4611686018427387900i']);
        runTestSet("public function main(x: Nat): Nat { return (2n // x) - 2n; }", [['1n', '0n']], ['2n', '0n']);
        runTestSet("public function main(x: Nat): Nat { return 2n // (x - 2n); }", [['4n', '1n']], ['1n', '2n']);

        runTestSet("public function main(x: ChkInt): ChkInt { return (x + 1I) * -4I; }", [['ChkInt::npos', 'ChkInt::npos']], []);
    });
});

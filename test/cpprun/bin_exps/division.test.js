"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple division", () => {
    it("should exec simple cases", function () {
        runTestSet("public function main(x: Nat): Nat { return 8n // x; }", [['4n', '2n'], ['1n', '8n']], ['0n']);
        runTestSet("public function main(x: Int): Int { return +2i // x; }", [['1i', '2i'], ['-2i', '-1i']], ['0i']);
    });
});

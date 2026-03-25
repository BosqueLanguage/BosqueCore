"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- simple abort", () => {
    it("should exec simple abort", function () {
        runTestSet("public function main(b: Bool): Int { if(b) { abort; } return 1i; }", [['false', '1i']], ['true']);
    });
});

describe ("CPPExec -- simple assert", () => {
    it("should exec simple assert", function () {
        runTestSet("public function main(x: Int): Int { assert x > 0i; return 1i; }", [['1i', '1i']], ['0i']);
    });
});

describe ("CPPExec -- simple validate", () => {
    it("should exec simple validate", function () {
        runTestSet("public function main(x: Int): Int { validate x == 3i; return 1i; }", [['3i', '1i']], ['0i']);
    });
});

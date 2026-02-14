"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- access argument", () => {
    it("should exec simple arg var access", function () {
        runTestSet("public function main(x: Int): Int { return x; }", [['5i', '5i']], []);
        runTestSet("public function main(y: Bool): Bool { let x = 3i; return y; }", [['true', 'true']], []);
    });
});

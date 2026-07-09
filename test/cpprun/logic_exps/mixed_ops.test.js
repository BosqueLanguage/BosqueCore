"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- logical mixed", () => {
    it("should exec simple mixed", function () {
        runTestSet("public function main(x: Bool): Bool { let y = x; return x && y || !x; }", [['true', 'true'], ['false', 'true']], []);
        runTestSet("public function main(x: Bool): Bool { let y = x; return !x && y || x; }", [['true', 'true'], ['false', 'false']], []);
    });
});

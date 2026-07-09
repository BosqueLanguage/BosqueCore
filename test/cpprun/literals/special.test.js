"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- special literals", () => {
    it("should exec true", function () {
        runTestSet("public function main(): Bool { return true; }", [[undefined, "true"]], []);
    });

    it("should exec false", function () {
        runTestSet("public function main(): Bool { return false; }", [[undefined, "false"]], []);
    });
});


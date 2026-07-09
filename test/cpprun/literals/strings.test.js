"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- String", () => {
    it("should exec simple strings", function () {
        runTestSet('public function main(): String { return ""; }', [[undefined, "\"\""]], []);
        runTestSet('public function main(): String { return "abc"; }', [[undefined, "\"abc\""]], []);
        //runTestSet('public function main(): String { return "a🌵c"; }', [[undefined, "\"a🌵c\""]], []);
    });

    it("should exec escaped strings", function () {
        runTestSet('public function main(): String { return "%x59;"; }', [[undefined, "\"Y\""]], []);
        //runTestSet('public function main(): String { return "%x1f335;"; }', [[undefined, "\"🌵\""]], []);
        //runTestSet('public function main(): String { return "%%;"; }', [[undefined, "\"%\""]], []);
        //runTestSet('public function main(): String { return "%;"; }', [[undefined, "\"\\\"\""]], []);
    });
});

describe ("CPPExec -- CString", () => {
    it("should exec simple cstrings", function () {
        runTestSet("public function main(): CString { return ''; }", [[undefined, "''"]], []);
        runTestSet("public function main(): CString { return 'abc'; }", [[undefined, "'abc'"]], []);
        
    });

    it("should exec escaped strings", function () {
        runTestSet("public function main(): CString { return '%x59;'; }", [[undefined, "'Y'"]], []);
        //runTestSet("public function main(): CString { return '%%;'; }", [[undefined, "'%'"]], []);
        //runTestSet("public function main(): CString { return '%;'; }", [[undefined, "'''"]], []);
    });
});

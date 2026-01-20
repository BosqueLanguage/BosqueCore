"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Special Constructor Some", () => {
    it("should exec ex some/option return", function () {
        runTestSet("public function main(x: Int): Some<Int> { return some(x); }", [['0i', 'some(0i)']], []);
        runTestSet("public function main(x: Int): Option<Int> { return some(x); }", [['0i', 'some(0i)']], []);
    });

    it("should exec some/option parse", function () {
        runTestSet("public function main(x: Some<Int>): Option<Int> { return x; }", [['some(0i)', 'some(0i)']], []);
        runTestSet("public function main(x: Option<Int>): Option<Int> { return x; }", [['none', 'none'], ['some(0i)', 'some(0i)']], []);
    });
});

describe ("CPPExec -- Special Constructor Option", () => {
    it("should exec none/option return", function () {
        runTestSet("public function main(x: None): None { return x; }", [['none', 'none']], []);
        runTestSet("public function main(y: Int): Option<Int> { let x = some(y); return x; }", [['3i', 'some(3i)']], []);
    });

    it("should exec nested option return", function () {
        runTestSet("public function main(x: None): Option<Option<Int>> { return x; }", [['none', 'none']], []);
        runTestSet("public function main(x: Some<Int>): Option<Option<Int>> { return some(x); }", [['none', 'none']], []);
        runTestSet("public function main(x: Option<Int>): Option<Option<Int>> { return some(x); }", [['none', 'some(none)'], ['some(0i)', 'some(some(0i))']], []);
    });
});

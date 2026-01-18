"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Regular Constructor Some", () => {
   it("should exec exec some/option return", function () {
        runTestSet("public function main(x: Int): Some<Int> { return Some<Int>(x); }", [['0i', 'some(0i)']], []);
        runTestSet("public function main(x: Int): Option<Int> { return Some<Int>(x); }", [['0i', 'some(0i)']], []);
    });

    it("should exec exec some/option parse", function () {
        runTestSet("public function main(x: Some<Int>): Option<Int> { return x; }", [['some(0i)', 'some(0i)']], []);
        runTestSet("public function main(x: Option<Int>): Option<Int> { return x; }", [['none', 'none'], ['some(0i)', 'some(0i)']], []);
    });
});

describe ("CPPExec -- Regular Constructor Option", () => {
    it("should exec exec none/option return", function () {
        runTestSet("public function main(x: None): None { return x; }", [['none', 'none']], []);
        runTestSet("public function main(y: Int): Option<Int> { let x = Some<Int>(y); return x; }", [['3i', 'some(3i)']], []);
    });

    it("should exec nested option return", function () {
        runTestSet("public function main(x: None): Option<Option<Int>> { return x; }", [['none', 'none']], []);
        runTestSet("public function main(x: Some<Int>): Option<Option<Int>> { return Some<Option<Int>>(x); }", [['none', 'none']], []);
        runTestSet("public function main(x: Option<Int>): Option<Option<Int>> { return Some<Option<Int>>(x); }", [['none', 'some(none)'], ['some(0i)', 'some(some(0i))']], []);
    });
});

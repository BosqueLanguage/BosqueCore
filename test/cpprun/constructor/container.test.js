"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Container Constructor (List)", () => {
    it("should exec simple list constructors", function () {
        runTestSet("public function main(x: Int): List<Int> { return List<Int>{}; }", [['5i', 'List<Int>{}']], []);
        runTestSet("public function main(x: Int): List<Int> { return List<Int>{x}; }", [['5i', 'List<Int>{5i}'], ['0i', 'List<Int>{0i}']], []);
        runTestSet("public function main(x: Int): List<Int> { return List<Int>{1i, x, 3i}; }", [['5i', 'List<Int>{1i, 5i, 3i}'], ['0i', 'List<Int>{1i, 0i, 3i}']], []);
    });

    it.skip("should exec spread and mixed list constructors", function () {
        runTestSet("public function main(l: List<Int>): List<Int> { return List<Int>{...l}; }", [], []);
        runTestSet("public function main(l: List<Int>): List<Int> { return List<Int>{...l, ...l}; }", [], []);
        runTestSet("public function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }", [], []);
    });
});

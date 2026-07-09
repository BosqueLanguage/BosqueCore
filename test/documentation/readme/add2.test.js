"use strict";

import { checkTestFunctionError, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

describe ("sub2 typechecks", () => {
    it("should typefail sub2 calls", function () {
        checkTestFunctionError('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(3i, 4.0f); }', "Argument y expected type Int but got Float"); 
        checkTestFunctionError('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(3, 4); }', "Un-annotated numeric literals are not supported"); 
    });
});

describe ("sub2 exec", () => {
    it("should exec sub2", function () {
        runTestSet('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(z: Int): Int { return sub2(z, 2i); }', [["4i", "2i"]], []); 
        runTestSet('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(z: Int): Int { return sub2(y=z, x=3i); }', [["2i", "1i"]], []); 
    });
});

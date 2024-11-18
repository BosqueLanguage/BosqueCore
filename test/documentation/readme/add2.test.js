"use strict";

import { checkTestFunctionInFileError, runMainCode } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

describe ("sub2 typechecks", () => {
    it("should create simple list", function () {
        checkTestFunctionInFileError('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(3i, 4.0f); }', "Argument y expected type Int but got Float"); 
        checkTestFunctionInFileError('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(3, 4); }', "Un-annotated numeric literals are not supported"); 
    });
});

describe ("sub2 exec", () => {
    it("should create simple list", function () {
        runMainCode('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(4i, 2i); }', [2n, "Int"]); 
        runMainCode('public function sub2(x: Int, y: Int): Int { return x - y; } public function main(): Int { return sub2(y=2i, 3i); }', [1n, "Int"]); 
    });
});

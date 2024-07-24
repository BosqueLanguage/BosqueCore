"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Constructable Constructor (Option)", () => {
    it("should check option constructors", function () {
        checkTestFunction("function main(): Int? { return Some<Int>{2i}; }");
    });

    it("should fail option constructors", function () {
        checkTestFunctionError("function main(): Int? { return Some<Int>{}; }", 'Some constructor expects 1 argument');
        checkTestFunctionError("function main(): Int? { return Some<Int>{2i, false}; }", 'Some constructor expects 1 argument');
    });
});

describe ("Checker -- Constructable Constructor (Result)", () => {
    it("should check result constructors", function () {
        checkTestFunction("function main(): Result<Int, Bool> { return Result<Int, Bool>::Ok{2i}; }");
        checkTestFunction("function main(): Result<Int, Bool> { return Result<Int, Bool>::Err{false}; }");
    });

    it("should fail result constructors", function () {
        checkTestFunctionError("function main(): Result<Int, Bool> { return Result<Int, Bool, Bool>::Ok{}; }", 'Type Ok expected 0 terms but got 3');

        checkTestFunctionError("function main(): Result<Int, Bool> { return Result<Int, Bool>::Ok{}; }", 'Ok constructor expects 1 argument');
        checkTestFunctionError("function main(): Result<Int, Bool> { return Result<Int, Bool>::Err{3i, false}; }", 'Err constructor expects 1 argument');
    });
});

describe ("Checker -- Constructable Constructor (Pair)", () => {
    it("should check pair constructors", function () {
        checkTestFunction("function main(): Pair<Int, Bool> { return Pair<Int, Bool>{2i, false}; }");
    });

    it("should fail pair constructors", function () {
        checkTestFunctionError("function main(): Pair<Bool> { return Pair<Int, Bool>{2i}; }", 'Type Pair expected 2 terms but got 1');

        checkTestFunctionError("function main(): Pair<Int, Bool> { return Pair<Int, Bool>{2i}; }", 'Pair constructor expects 2 arguments');
        checkTestFunctionError("function main(): Pair<Int, Bool> { return Pair<Int, Bool>{2i, 3i, 4i}; }", 'Pair constructor expects 2 arguments');
    });
});

describe ("Checker -- Constructable Constructor (MapEntry)", () => {
    it("should check entry constructors", function () {
        checkTestFunction("function main(): MapEntry<Int, Bool> { return MapEntry<Int, Bool>{2i, true}; }");
    });

    it("should fail entry constructors", function () {
        checkTestFunctionError("function main(): MapEntry<Int, Bool> { return MapEntry<Int, Bool>{2i}; }", 'MapEntry constructor expects 2 arguments');
        checkTestFunctionError("function main(): MapEntry<Int, Bool> { return MapEntry<Int, Bool>{2i, 3i, 4i}; }", 'MapEntry constructor expects 2 arguments');
    });
});

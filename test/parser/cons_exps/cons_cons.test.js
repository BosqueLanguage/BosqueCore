"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Constructable Constructor (Option)", () => {
    it("should parse option constructors", function () {
        parseTestFunction("function main(): Option<Int> { return Some<Int>{2i}; }", undefined);
    });

    it("should fail option constructors", function () {
        parseTestFunctionError("function main(): Option<Int> { return Some<>{}; }", 'Template term list cannot be empty');
        
        parseTestFunctionError("function main(): Option<Int> { return Some<Int>{; }", 'Unexpected token in expression -- ;');
        parseTestFunctionError("function main(): Option<Int> { return Some<Int>2i, false}; }", 'Unknown type scoped expression');
    });
});

describe ("Parser -- Constructable Constructor (Result)", () => {
    it("should parse result constructors", function () {
        parseTestFunction("function main(): Result<Int, Bool> { return Result<Int, Bool>::Ok{2i}; }", undefined);
        parseTestFunction("function main(): Result<Int, Bool> { return Result<Int, Bool>::Fail{false}; }", undefined);
    });
});

describe ("Parser -- Constructable Constructor (MapEntry)", () => {
    it("should parse entry constructors", function () {
        parseTestFunction("function main(): MapEntry<Int, Bool> { return MapEntry<Int, Bool>{2i, true}; }", undefined);
    });

    it("should fail entry constructors", function () {
        parseTestFunctionError("function main(): MapEntry<Int, Bool> { return 2i => false; }", 'Expected ";" but got " => " when parsing "line statement"');
    });
});

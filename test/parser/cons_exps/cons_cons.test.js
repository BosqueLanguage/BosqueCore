"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Constructable Constructor (Option)", () => {
    it("should parse option constructors", function () {
        parseTestFunction("function main(): Int? { return Some<Int>{2i}; }", undefined);
    });

    it("should fail option constructors", function () {
        checkTestFunctionError("function main(): Int? { return Some<>{}; }", 'err5');
        
        parseTestFunctionError("function main(): Int? { return Some<Int>{; }", 'Unexpected token in expression -- ;');
        parseTestFunctionError("function main(): Int? { return Some<Int>2i, false}; }", 'Unknown type scoped expression');
    });
});

describe ("Parser -- Constructable Constructor (Result)", () => {
    it("should parse result constructors", function () {
        parseTestFunction("function main(): Result<Int, Bool> { return Result<Int, Bool>::Ok{2i}; }", undefined);
        parseTestFunction("function main(): Result<Int, Bool> { return Result<Int, Bool>::Err{false}; }", undefined);
    });
});

describe ("Parser -- Constructable Constructor (Pair)", () => {
    it("should parse pair constructors", function () {
        parseTestFunction("function main(): Pair<Int, Bool> { return Pair<Int, Bool>{2i, false}; }", undefined);
    });

    it("should fail pair constructors", function () {
        parseTestFunctionError("function main(): Pair<Int Bool> { return Pair<Int, Bool>{2i, 3i, 4i}; }", 'Expected ">" but got "[RECOVER]" when parsing "template term list"');
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

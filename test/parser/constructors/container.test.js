"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Container Constructor (List)", () => {
    it("should parse list constructors", function () {
        parseTestFunction("function main(): List<Int> { return List<Int>{}; }", undefined);
        parseTestFunction("function main(): List<Int> { return List<Int>{1i, 2i, 3i}; }", undefined);
        parseTestFunction("function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }", undefined);
    });

    it("should fail list constructors", function () {
        parseTestFunctionError("function main(x: Int): List<Int> { return List<Int>{ref x}; }", 'Cannot have a special passing argument in collection constructor context');
        parseTestFunctionError("function main(): List<Int> { return List<Int>{x=2i}; }", 'Cannot have named arguments in collection constructor');
    });

    it("should parse map constructors", function () {
        parseTestFunction("function main(): Map<Int, Nat> { return Map<Int, Nat>{}; }", undefined);
        parseTestFunction("function main(): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n, MapEntry{3i, 4n}}; }", undefined);
        parseTestFunction("function main(m: Map<Int, Nat>): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n, ...m, 3i => 4n}; }", undefined);
    });

    it("should fail map constructors", function () {
        parseTestFunctionError("function main(x: Int): Map<Int, Nat> { return Map<Int, Nat>{ref x => 2n}; }", 'Cannot have a special passing argument in collection constructor context');
        parseTestFunctionError("function main(): Map<Int, Nat> { return Map<Int, Nat>{x=2n}; }", 'Cannot have named arguments in collection constructor');
    });
});

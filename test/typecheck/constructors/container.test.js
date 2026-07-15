"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Container Constructor (List)", () => {
    it("should check list constructors", function () {
        checkTestFunction("function main(): List<Int> { return List<Int>{}; }");
        checkTestFunction("function main(): List<Int> { return List<Int>{1i, 2i, 3i}; }");
        checkTestFunction("function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }");
    });

    it("should fail list constructors", function () {
        checkTestFunctionError("function main(): List<Int> { return List<Int>{2n}; }", 'Argument 0 expected type Int');
    });

    it("should check map constructors", function () {
        checkTestFunction("function main(): Map<Int, Nat> { return Map<Int, Nat>{}; }");
        checkTestFunction("function main(): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n, MapEntry<Int, Nat>{3i, 4n}}; }");
        checkTestFunction("function main(m: Map<Int, Nat>): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n, ...m, 3i => 4n}; }");
    });

    it("should fail map constructors", function () {
        checkTestFunctionError("function main(): Map<Int, Nat> { return Map<Int, Nat>{2n => 3n}; }", 'MapEntryConstructor key expression is not a subtype of Int');
        checkTestFunctionError("function main(): Map<Int, Nat> { return Map<Int, Nat>{2n}; }", 'Argument 0 expected type MapEntry<Int, Nat>');
        checkTestFunctionError("function main(): Map<Float, Nat> { return Map<Float, Nat>{ 2.0f => 3n }; }", 'Template argument K is not a keytype');
    });
});

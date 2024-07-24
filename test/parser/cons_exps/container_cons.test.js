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
        parseTestFunctionError("function main(x: Int): List<Int> { return List<Int>{ref x}; }", 'Cannot have a reference argument in this context');
    });
});

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
        parseTestFunctionError("function main(): Option<Int> { return Some<Int>2i, false}; }", 'Unknown member ;');
    });
});

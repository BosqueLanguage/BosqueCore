"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- elist return", () => {
    it("should parse elist returns", function () {
        parseTestFunctionInFile('[FUNC]', 'function main(): (|Int, Bool|) { return (|2i, true|); }');
        parseTestFunctionInFile('[FUNC]', 'function main(): (|Int, Bool|) { return 2i, true; }');
    });

    it("should parse fail elist returns", function () {
        parseTestFunctionInFileError('function main(): (|Int, Bool|) { return 2i true; }', 'Expected ";" but got "true" when parsing "line statement"');
    });
});

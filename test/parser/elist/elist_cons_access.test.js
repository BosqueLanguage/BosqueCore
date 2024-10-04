"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- elist decl and access", () => {
    it("should parse simple elist", function () {
        parseTestFunctionInFile('[FUNC]', 'function main(): Int { return (|2i, true|).0; }'); 
    });

    it("should parse fail simple elist", function () {
        parseTestFunctionInFileError('function main(): Int { return (|2i, true|).0n; }', 'Expected "[IDENTIFIER]" but got "0n" when parsing "postfix access/invoke"');
        parseTestFunctionInFileError('function main(): Int { return (|2i, true|)0; }', 'Expected ";" but got "0" when parsing "line statement"');
        parseTestFunctionInFileError('function main(): Int { return (|2i true|).0; }', 'Expected "|)" but got "[RECOVER]" when parsing "elist constructor expression"');
    });
});


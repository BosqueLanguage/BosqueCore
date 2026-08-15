"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Task Declarations", () => {
    it("should parse simple task decl", function () {
        parseTestFunctionInFile('public task Main { field x: Int; action main(): Int { return 1i; } } [FUNC]', 'function main(): Int { return 1i; }');
    });
});

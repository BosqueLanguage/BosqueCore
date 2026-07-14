"use strict";

import { parseTestExp, parseTestFunction, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- ref updates", () => {
    it("should parse ref updates", function () {
        parseTestFunction('function foo(ref x: Int): Int { return x; }', undefined);
    });

    it("should fail ref updates", function () {
        parseTestFunctionInFileError('function foo(ref x: Int): Int { return x; } function main(): Int { var y: Int = 0i; return foo(ref x = 1i); }', "Could not resolve 'x' in this context");
    });
});

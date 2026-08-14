"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Agent Declarations", () => {
    it("should parse simple agent api", function () {
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { return; }');
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { return 1i; }');
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int requires n != 0n; ensures $return > 0i; ;[FUNC]', 'function main(): Int { return 1i; }');
    });
});


describe ("Parser -- Agent Calls", () => {
    it("should parse simple agent call", function () {
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { return agent foo(3n); }');
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { let ii = agent Main::foo(3n); return ii; }');

        parseTestFunctionInFile('abstract agent foo(n: Nat): CString; [FUNC]', 'function main(): Int { return agent foo<Int>(3n); }');
    });
});
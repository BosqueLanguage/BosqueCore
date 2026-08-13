"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Agent Declarations", () => {
    it("should parse simple agent api", function () {
        parseTestFunctionInFile('agent foo(n: Nat): APIResult<Int, CString>; [FUNC]', 'function main(): Int { return; }');
        parseTestFunctionInFile('agent foo(n: Nat): APIResult<Int, CString>; [FUNC]', 'function main(): Int { return 1i; }');
        parseTestFunctionInFile('agent foo(n: Nat): APIResult<Int, CString> requires n != 0n; ensures ($return)@success ==> $$return.value > 0i; [FUNC]', 'function main(): Int { return 1i; }');
    });
});


describe ("Parser -- Agent Calls", () => {
    it("should parse simple agent call", function () {
        parseTestFunctionInFile('agent foo(n: Nat): APIResult<Int, CString>; [FUNC]', 'function main(): Int { let ii = agent foo(3n); return ii@success; }');
        parseTestFunctionInFile('agent foo(n: Nat): APIResult<Int, CString>; [FUNC]', 'function main(): Int { let ii = agent Main::foo(3n); return ii@success; }');

        parseTestFunctionInFile('agent foo(n: Nat): APIResult<Int, CString>; [FUNC]', 'function main(): Int { agent foo(3n); return; }');
        parseTestFunctionInFile('agent foo(n: Nat): APIResult<Int, CString> requires n != 0n; ensures ($return)@success ==> $$return > 0i; [FUNC]', 'function main(): Int { let ii = agent foo(3n); return ii@success; }');
    });
});
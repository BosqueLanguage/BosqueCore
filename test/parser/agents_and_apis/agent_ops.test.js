"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Agent Declarations", () => {
    it("should parse simple agent decl", function () {
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { return; }');
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { return 1i; }');
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int requires n != 0n; ensures $return > 0i; ;[FUNC]', 'function main(): Int { return 1i; }');
    });

    it("should parse simple agent decl fail", function () {
        parseTestFunctionInFileError('agent foo(n: Nat): Int; function main(): Int { return; }', "Body implementation expected unless declared as abstract");
        parseTestFunctionInFileError('abstract agent foo(out n: Nat): Int; function main(): Int { return 1i; }', 'Cannot have special passing parameter here');
    });
});

describe ("Parser -- Agent Calls", () => {
    it("should parse simple agent call", function () {
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { return agent Main::foo(env{}, 3n); }');
        parseTestFunctionInFile('abstract agent foo(n: Nat): Int; [FUNC]', 'function main(): Int { let ii = agent Main::foo(env{}, 3n); return ii; }');

        parseTestFunctionInFile('abstract agent foo(n: Nat): CString; [FUNC]', 'function main(): Int { return agent Main::foo<Int>(env{}, 3n); }');
    });

    it("should parse simple agent call fail", function () {
        parseTestFunctionInFileError('abstract agent foo(n: Nat): Int; function main(): Int { return agent Main::foo(, 3n); }', "Unexpected token in expression -- ,");
        parseTestFunctionInFileError('abstract agent foo(n: Nat): Int; function main(): Int { return agent Main::foo(env{} 3n); }', 'Expected ")" but got "3n" when parsing "Task arguments"');
    });
});

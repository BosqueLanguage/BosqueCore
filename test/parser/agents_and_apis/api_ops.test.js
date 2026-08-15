"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- API Declarations", () => {
    it("should parse simple api decl", function () {
        parseTestFunctionInFile('abstract api foo(n: Nat): Int; [FUNC]', 'function main(): Int { return; }');
        parseTestFunctionInFile('abstract api foo(n: Nat): Int; [FUNC]', 'function main(): Int { return 1i; }');
        parseTestFunctionInFile('abstract api foo(n: Nat): Int requires n != 0n; ensures $return > 0i; ;[FUNC]', 'function main(): Int { return 1i; }');
    });

    it("should parse simple api decl fail", function () {
        parseTestFunctionInFileError('api foo(n: Nat): Int; function main(): Int { return; }', "Body implementation expected unless declared as abstract");
    });
});

describe ("Parser -- API Calls", () => {
    it("should parse simple api call", function () {
        parseTestFunctionInFile('abstract api foo(n: Nat): Int; [FUNC]', 'function main(): Int { return api Main::foo(env{}, 3n); }');
        parseTestFunctionInFile('abstract api foo(n: Nat): Int; [FUNC]', 'function main(): Int { let ii = api Main::foo(env{}, 3n); return ii; }');
    });

    it("should parse simple api call fail", function () {
        parseTestFunctionInFileError('abstract api foo(n: Nat): Int; function main(): Int { return api Main::foo(, 3n); }', "Unexpected token in expression -- ,");
        parseTestFunctionInFileError('abstract api foo(n: Nat): Int; function main(): Int { return api Main::foo(env{} 3n); }', 'Expected ")" but got "3n" when parsing "Task arguments"');
    });
});

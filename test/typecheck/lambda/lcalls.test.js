"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Lambda calls (no template)", () => {
    it("should check simple lambda full", function () {
        checkTestFunctionInFile("function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Int { return foo(fn(x: Int): Int => { return x + 1i; }); }");
    });

    it("should check simple lambda infer", function () {
        checkTestFunctionInFile("function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Int { return foo(fn(x): Int => { return x + 1i; }); }");
        checkTestFunctionInFile("function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Int { return foo(fn(x: Int) => { return x + 1i; }); }");
        checkTestFunctionInFile("function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Int { return foo(fn(x) => { return x + 1i; }); }");
    });

    it("should check lambda capture", function () {
        checkTestFunctionInFile("function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Int { let y = 1i; return foo(fn(x) => { return x + y; }); }");

        checkTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { return x + y; }, 2i); }');
    });

    it("should fail types", function () {
        checkTestFunctionInFileError("function foo(f: fn(Int) -> Bool): Int { return f(1i); } function main(): Int { return foo(fn(x) => { return x + 1i; }); }", "Expected a return value of type Int but got Bool");
        checkTestFunctionInFileError("function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Int { return foo(fn() => { return 1i; }); }", "Cannot infer type for lambda constructor");
    });

    it("should fail pred", function () {
        checkTestFunctionInFileError("function foo(f: pred(Int) -> Int): Int { return f(1i); } function main(): Bool { return foo(pred(x) => { return x + 1i; }); }", "Lambda pred must have a boolean return type");
    });
});

describe ("Checker -- Lambda calls (with template)", () => {
    it("should check simple positional", function () {
        checkTestFunctionInFile("function foo<T>(x: T, f: fn(T) -> T): T { return f(x); } function main(): Int { return foo<Int>(3i, fn(x) => x); }");
    });
});

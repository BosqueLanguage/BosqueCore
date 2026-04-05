"use strict";

import { checkTestFunctionInFile } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Lambda ref calls", () => {
    it("should check simple ref full", function () {
        checkTestFunctionInFile('function foo(f: fn(inout Int) -> Int): Int { var x = 1i; return f(inout x); } function main(): Int { return foo(fn(inout x: Int): Int => x); }');
        checkTestFunctionInFile('entity Foo { field v: Int; } function foo(f: fn(ref Foo) -> Int): Int { var x = Foo{ 1i }; return f(ref x); } public function main(): Int { return foo(fn(ref x: Foo): Int => x.v); }');
    });

    it("should check fail ref and skip", function () {
        checkTestFunctionInFile('function foo(f: fn(inout Int) -> Int): Int { var x = 1i; return f(inout x); } function main(): Int { return foo(fn(inout x): Int => x); }');
        checkTestFunctionInFile('function foo(f: fn(inout Int) -> Int): Int { var x = 1i; return f(inout x); } function main(): Int { return foo(fn(inout x: Int) => x); }');
        checkTestFunctionInFile('function foo(f: fn(inout Int) -> Int): Int { var x = 1i; return f(inout x); } function main(): Int { return foo(fn(inout x) => x); }');
    });
});

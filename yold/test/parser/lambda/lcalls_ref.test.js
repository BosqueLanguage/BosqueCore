"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Lambda ref calls", () => {
    it("should parse simple ref full", function () {
        parseTestFunctionInFile('entity Foo { field v: Int; } function foo(f: fn(ref Foo) -> Int): Int { let x = Foo{ 1i }; return f(ref x); } [FUNC]', 'function main(): Bool { return foo(fn(ref x: Foo): Int => x.v); }');
    });

    it("should parse simple ref infer", function () {
        parseTestFunctionInFile('entity Foo { field v: Int; } function foo(f: fn(ref Foo) -> Int): Int { let x = Foo{ 1i }; return f(ref x); } [FUNC]', 'function main(): Bool { return foo(fn(ref x) => { return x.v; }); }');
    });
});


"use strict";

import { checkTestFunctionInFile } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Postfix Chains", () => {
    it("should check simple postfix chains", function () {
        checkTestFunctionInFile('entity Foo { field f: Int; } entity Bar { field g: Foo; } function main(): Int { return Bar{Foo{3i}}.g.f; }'); 
        checkTestFunctionInFile('type Bar = Int; entity Foo { field f: Bar; } function main(): Int { let x = Foo{Bar{3i}}; return x.f.value; }'); 

        checkTestFunctionInFile('entity Foo { method f(x: Int): Int { return x; } } entity Bar { field g: Foo; } function main(): Int { return Bar{Foo{}}.g.f(1i); }'); 
    });

    it("should check postfix chains w/ ref", function () {
        checkTestFunctionInFile('entity Foo { method f(inout x: Int): Int { return x; } } entity Bar { field g: Foo; } function main(): Int { var y: Int = 0i; return Bar{Foo{}}.g.f(inout y); }'); 
    });
});

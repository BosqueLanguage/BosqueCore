"use strict";

import { checkTestFunctionInFile } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";


describe ("Checker -- Void NamespaceFunction Ref Params", () => {
    it("should check simple ref", function () {
        checkTestFunctionInFile('entity Foo{ } function foo(ref y: Foo) { return; } public function main(): Int { var ff = Foo{}; foo(ref ff); return 1i; }');    
    });
});

describe ("Checker -- Void method Ref Params", () => {
    it("should check simple ref", function () {
        checkTestFunctionInFile('entity Foo{ ref method foo() { return; } } public function main(): Int { var ff = Foo{}; ref ff.foo(); return 1i; }');    
    });
});


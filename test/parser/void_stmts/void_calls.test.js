"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Void NamespaceFunction Ref Params", () => {
    it("should parse simple ref", function () {
        parseTestFunctionInFile('entity Foo{ } function foo(ref y: Foo) { return; } [FUNC]', 'function main(): Int { let ff = Foo{}; foo(ref ff); return 1i; }');    
    });
});

describe ("Parser -- Void method Ref Params", () => {
    it("should parse simple ref", function () {
        parseTestFunctionInFile('entity Foo{ ref method foo() { return; } } [FUNC]', 'function main(): Int { let ff = Foo{}; ref ff.foo(); return 1i; }');    
    });
});


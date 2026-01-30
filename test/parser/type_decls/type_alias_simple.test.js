"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- type decl of bool", () => {
    it("should parse bool type decl", function () {
        parseTestFunctionInFile('type Flag = Bool; [FUNC]', 'function main(): Flag { return true<Flag>; }'); 
    });

});

describe ("Parser -- type decl of number", () => {
    it("should parse numeric type decls", function () {
        parseTestFunctionInFile('type NVal = Int; [FUNC]', 'function main(): NVal { return -2i<NVal>; }');
        parseTestFunctionInFile('type FVal = Float; [FUNC]', 'function main(): FVal { return 0.0f<FVal>; }');    
    });
});

describe ("Parser -- type decl of number with invariants", () => {
    it("should parse numeric type decls", function () {
        parseTestFunctionInFile('type NVal = Int & { invariant $value > 0i; invariant $value <= 100i; } [FUNC]', 'function main(): Int { let x = -2i<NVal>; return 5i; }');    
    });
});

describe ("Parser -- type decl with consts", () => {
    it("should parse entity with consts", function () {
        parseTestFunctionInFile('type Foo = Int & { const c: Int = 3i; } [FUNC]', 'function main(): Int { return Foo::c; }'); 
    });

    it("should parse entity with consts errors", function () {
        parseTestFunctionInFileError('type Foo = Int & { field c: Int; } function main(): Nat { return 4n; }', "Cannot have a field member on this type"); 
    });
});

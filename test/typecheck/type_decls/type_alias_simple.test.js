"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- type decl of bool", () => {
    it("should check bool type decl", function () {
        checkTestFunction('type Flag = Bool; function main(): Flag { return true<Flag>; }'); 
    });

    it("should fail not bool", function () {
        checkTestFunctionError("type Flag = Bool; function main(): Flag { return 3i<Flag>; }", "Literal value is not the same type (Int) as the value type (Bool)");
    });
});

describe ("Checker -- type decl of number", () => {
    it("should check numeric type decls", function () {
        checkTestFunction('type NVal = Int; function main(): NVal { return -2i<NVal>; }');
        checkTestFunction('type FVal = Float; function main(): FVal { return 0.0f<FVal>; }');    
    });

    it("should fail not int", function () {
        checkTestFunctionError("type NVal = Int; function main(): NVal { return 3n<NVal>; }", "Literal value is not the same type (Nat) as the value type (Int)");
    });
});

describe ("Checker -- type decl of number with invariants", () => {
    it("should check positional", function () {
        checkTestFunctionInFile('type Foo = Int & { invariant $value > 3i; } function main(): Foo { return Foo{1i}; }');
    });

    it("should fail missing names", function () {
        checkTestFunctionInFileError('type Foo = Int & { invariant $g > 3i; } function main(): Foo { return Foo{1i}; }', 'Variable $g is not declared here');
    });

    it("should fail bool", function () {
        checkTestFunctionInFileError('type Foo = Int & { invariant $value; } function main(): Foo { return Foo{3i}; }', 'Invariant expression does not have a boolean type -- got Int');
    });
});

describe ("Checker -- type decl of number with value", () => {
    it("should check numeric type decls", function () {
        checkTestFunction('type NVal = Int; function main(): NVal { let x = -2i<NVal>; return x; }');    
    });

    it("should fail not nat", function () {
        checkTestFunctionError('type II = Int; type NVal = II; function main(): Int { return 2i; }', "In type declaration value type must be simple primitive -- Bool, Int, etc.");
    });
});

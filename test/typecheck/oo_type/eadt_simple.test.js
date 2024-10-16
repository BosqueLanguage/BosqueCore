"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";


describe ("Checker -- eADT decl", () => {
    it("should check simple eADT", function () {
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } | F2 { }; function main(): Int { return F1{3i}.f; }'); 
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; function main(): Bool { return F2{false}.g; }'); 

        checkTestFunctionInFile('datatype Foo<T> of F1 { field f: T; } | F2 { }; function main(): Int { return F1<Int>{3i}.f; }'); 
    });

    it("should check fail simple eADT", function () {
        checkTestFunctionInFileError('datatype Foo of F1 { field f: Int; } | F2 { }; function main(): Nat { return F1{3i}.f; }', 'Expected a return value of type Nat but got Int');
        checkTestFunctionInFileError('datatype Foo of F1 { field f: Int; } | F2 { }; function main(): Int { return F1{3i}.g; }', 'Could not find field g in type F1');

        checkTestFunctionInFileError('datatype Foo<T> of F1 { field f: T; } | F2 { }; function main(): Int { return F1<Nat>{3i}.f; }', 'Argument f expected type Nat but got Int');

        checkTestFunctionInFileError('datatype Foo<T> of F1 { field f: T; } | F2 { }; function main(): Int { return Foo<Int>{3i}.f; }', 'Invalid type for constructor expression -- Foo<Int>'); 
    });

    it("should check eADT const", function () {
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } function main(): Int { return F1::c; }'); 
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } function main(): Int { return Foo::c; }'); 

        checkTestFunctionInFileError('datatype Foo of F1 { field f: Int; } | F2 { field: c: Nat; } & { const c: Int = 3i; } function main(): Int { return Foo::c; }', "cerr111"); 
    });

    it("should check eADT function", function () {
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } | F2 { } & { function foo: Int { return 3i; } } function main(): Int { return F1::foo(); }'); 
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } | F2 { } & { function foo: Int { return 3i; } } function main(): Int { return Foo::foo(); }'); 
    });
});

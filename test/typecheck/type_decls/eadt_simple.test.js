"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- eADT decl", () => {
    it("should check simple eADT", function () {
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } F2 { }; function main(): Int { return F1{3i}.f; }'); 
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; invariant $f >= 0i; } F2 { field g: Bool; }; function main(): Bool { return F2{false}.g; }'); 

        checkTestFunctionInFile('datatype Foo<T> of F1 { field f: T; } F2 { }; function main(): Int { return F1<Int>{3i}.f; }'); 
    });

    it("should check fail simple eADT", function () {
        checkTestFunctionInFileError('datatype Foo of F1 { field f: Int; } F2 { }; function main(): Nat { return F1{3i}.f; }', 'Expected a return value of type Nat but got Int');
        checkTestFunctionInFileError('datatype Foo of F1 { field f: Int; } F2 { }; function main(): Int { return F1{3i}.g; }', 'Could not find field g in type F1');

        checkTestFunctionInFileError('datatype Foo<T> of F1 { field f: T; } F2 { }; function main(): Int { return F1<Nat>{3i}.f; }', 'Argument f expected type Nat but got Int');

        checkTestFunctionInFileError('datatype Foo<T> of F1 { field f: T; } F2 { }; function main(): Int { return Foo<Int>{3i}.f; }', 'Invalid type for constructor expression -- Foo<Int>'); 
    });

    it("should check eADT const", function () {
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } F2 { } & { const c: Int = 3i; } function main(): Int { return F1::c; }'); 
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } F2 { } & { const c: Int = 3i; } function main(): Int { return Foo::c; }'); 
    });

    it("should check eADT function", function () {
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } F2 { } & { function foo(): Int { return 3i; } } function main(): Int { return F1::foo(); }'); 
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } F2 { } & { function foo(): Int { return 3i; } } function main(): Int { return Foo::foo(); }'); 
    });

    it("should check eADT function w/ multiple", function () {
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; function foo<T>(x: T): Option<T> { return some(x); } } F2 { } & { function foo(): Int { return 3i; } } function main(): Int { return F1::foo(); }'); 
        checkTestFunctionInFile('datatype Foo of F1 { field f: Int; function foo<T>(x: T): Option<T> { return some(x); } } F2 { } & { function foo(): Int { return 3i; } } function main(): Int { return F1::foo<Int>(3i).@some; }'); 
    });
});

describe ("Checker -- entity decl inherits", () => {
    it("should check simple inherits eADT", function () {
        checkTestFunctionInFile('datatype Foo using { field f: Int; } of F1 { } F2 { }; function main(): Int { return F1{3i}.f; }'); 
        checkTestFunctionInFile('datatype Foo using { field f: Int; invariant $f >= 0i; } of F1 { } F2 { field g: Bool; }; function main(): Bool { return F2{3i, false}.g; }'); 

        checkTestFunctionInFile('datatype Foo<T> using { field f: T; } of F1 { } F2 { }; function main(): Int { return F1<Int>{3i}.f; }'); 

        checkTestFunctionInFile('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } F2 { }; function main(): Int { return F1{3i, true}.f; }'); 
    });

    it("should check fail simple inherits eADT", function () {
        checkTestFunctionInFileError('datatype Foo using { field f: Int; } of F1 { } F2 { }; function main(): Nat { return F1{3i}.f; }', "Expected a return value of type Nat but got Int"); 

        checkTestFunctionInFileError('datatype Foo<T> using { field f: T; } of F1 { } F2 { }; function main(): Int { return F1<Int>{3n}.f; }', "Argument f expected type Int but got Nat"); 

        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0n; } F2 { }; function main(): Int { return F1<Int>{3i, true}.f; }', "Type F1 expected 0 terms but got 1"); 

        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0n; } F2 { }; function main(): Int { return F1{3i, true}.f; }', "Operator >= requires 2 arguments of the same type"); 
        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } F2 { }; function main(): Int { return F1{true, 3i}.f; }', "Argument f expected type Int but got Bool"); 

        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } F2 { }; function main(): Nat { return F1{3i, false}.f; }', "Expected a return value of type Nat but got Int"); 
    });
});

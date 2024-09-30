"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- entity decl inherits", () => {
    it("should check simple inherits eADT", function () {
        checkTestFunctionInFile('datatype Foo using { field f: Int; } of F1 { } | F2 { }; function main(): Int { return F1{3i}.f; }'); 
        checkTestFunctionInFile('datatype Foo using { field f: Int; invariant $f >= 0i; } of F1 { } | F2 { field g: Bool; }; function main(): Bool { return F2{3i, false}.g; }'); 

        checkTestFunctionInFile('datatype Foo<T> using { field f: T; } of F1 { } | F2 { }; function main(): Int { return F1<Int>{3i}.f; }'); 

        checkTestFunctionInFile('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } | F2 { }; function main(): Int { return F1{3i, true}.f; }'); 
    });

    it("should check fail simple inherits eADT", function () {
        checkTestFunctionInFileError('datatype Foo using { field f: Int; } of F1 { } | F2 { }; function main(): Nat { return F1{3i}.f; }', "Expected a return value of type Nat but got Int"); 

        checkTestFunctionInFileError('datatype Foo<T> using { field f: T; } of F1 { } | F2 { }; function main(): Int { return F1<Int>{3n}.f; }', "Argument f expected type Int but got Nat"); 

        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0n; } | F2 { }; function main(): Int { return F1<Int>{3i, true}.f; }', "Type F1 expected 0 terms but got 1"); 

        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0n; } | F2 { }; function main(): Int { return F1{3i, true}.f; }', "err44"); 
        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } | F2 { }; function main(): Int { return F1{true, 3i}.f; }', "err55"); 

        checkTestFunctionInFileError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } | F2 { }; function main(): Nat { return F1{3i, false}.f; }', "err55"); 
    });
});

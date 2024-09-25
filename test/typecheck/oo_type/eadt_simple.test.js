"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

it("should check simple eADT", function () {
    checkTestFunctionInFile('datatype Foo of F1 { field f: Int; } | F2 { }; function main(): Int { return F1{3i}.f; }'); 
    checkTestFunctionInFile('datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; function main(): Bool { return F2{false}.g; }'); 

    checkTestFunctionInFile('datatype Foo<T> of F1 { field f: T; } | F2 { }; function main(): Int { return Foo<Int>{3i}.f; }'); 
});

it("should check fail simple eADT", function () {
    checkTestFunctionInFileError('datatype Foo of F1 { field f: Int; } | F2 { }; function main(): Nat { return F1{3i}.f; }', 'err8');
    checkTestFunctionInFileError('datatype Foo of F1 { field f: Int; } | F2 { }; function main(): Int { return F1{3i}.g; }', 'er9');

    checkTestFunctionInFileError('datatype Foo<T> of F1 { field f: T; } | F2 { }; function main(): Int { return F1<Nat>{3i}.f; }', 'errt');
});
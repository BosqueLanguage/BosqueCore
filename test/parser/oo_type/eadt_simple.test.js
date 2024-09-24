"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- eADT decl", () => {
    it("should parse simple eADT", function () {
        parseTestFunctionInFile('datatype Foo of F1 { field f: Int; } | F2 { }; [FUNC]', 'function main(): Int { return F1{3i}.f; }'); 
        parseTestFunctionInFile('datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; [FUNC]', 'function main(): Bool { return F2{false}.g; }'); 

        parseTestFunctionInFile('datatype Foo<T> of F1 { field f: T; } | F2 { }; [FUNC]', 'function main(): Int { return Foo<Int>{3i}.f; }'); 
    });

    it("should parse fail simple eADT", function () {
        parseTestFunctionInFileError('datatype Foo of F1 { field f: Int; } F2 { }; function main(): Int { return F1{3i}.f; }', "err3");
        parseTestFunctionInFileError('datatype Foo of F1 { field f: Int; } | F2 { } function main(): Int { return F1{3i}.f; }', "err4");

        parseTestFunctionInFileError('datatype Foo<T> of F1<U> { field f: T; } | F2 { }; function main(): Int { return F1{3i}.f; }', "err5");
    });
});


"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- eADT decl", () => {
    it("should parse simple inherits eADT", function () {
        parseTestFunctionInFile('datatype Foo using { field f: Int; } of F1 { } | F2 { }; [FUNC]', 'function main(): Int { return F1{3i}.f; }'); 
        parseTestFunctionInFile('datatype Foo using { field f: Int; invariant $f >= 0i; } of F1 { } | F2 { field g: Bool; }; [FUNC]', 'function main(): Bool { return F2{3i, false}.g; }'); 

        parseTestFunctionInFile('datatype Foo<T> using { field f: T; } of F1 { } | F2 { }; [FUNC]', 'function main(): Int { return F1<Int>{3i}.f; }'); 

        parseTestFunctionInFile('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } | F2 { }; [FUNC]', 'function main(): Int { return F1<Int>{3i, true}.f; }'); 
    });

    it("should parse fail simple inherits eADT", function () {
        parseTestFunctionInFileError('datatype Foo { field f: Int; } of F1 { } | F2 { }; function main(): Int { return F1{3i}.f; }', 'Missing clause in datatype declaration');
    });
});


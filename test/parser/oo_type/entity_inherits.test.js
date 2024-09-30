"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- entity decl inherits", () => {
    it("should parse simple entity inherits fields", function () {
        parseTestFunctionInFile('concept Foo { field f: Int; } entity Bar provides Foo { } [FUNC]', 'function main(): Int { return Bar{3i}.f; }'); 
        parseTestFunctionInFile('concept Foo { field f: Int; } entity Bar provides Foo { field g: Bool; } [FUNC]', 'function main(): Bool { return Bar{3i, true}.g; }'); 
        parseTestFunctionInFile('concept Foo { field f: Int; } concept Baz { field g: Bool; } entity Bar provides Foo, Baz { } [FUNC]', 'function main(): Int { return Bar{3i, true}.f; }'); 

        parseTestFunctionInFile('concept Foo<T> { field f: T; } entity Bar<T> provides Foo<T> { } [FUNC]', 'function main(): Int { return Bar<Int>{3i}.f; }'); 
        parseTestFunctionInFile('concept Foo<U> { field f: U; } entity Bar<T> provides Foo<T> { } [FUNC]', 'function main(): Int { return Bar<Int>{3i}.f; }'); 
    });

    it("should parse simple entity inherits fields and invariants", function () {
        parseTestFunctionInFile('concept Foo { field f: Int; invariant $f > 0i; } entity Bar provides Foo { } [FUNC]', 'function main(): Int { return Bar{3i}.f; }');
        parseTestFunctionInFile('concept Foo { field f: Int; } entity Bar provides Foo { invariant $f > 0i; } [FUNC]', 'function main(): Int { return Bar{3i}.f; }'); 

        parseTestFunctionInFile('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } [FUNC]', 'function main(): Int { return Bar{3i}.f; }'); 
    });

    it("should parse fail simple entity inherits", function () {
        parseTestFunctionInFileError('concept Foo { field f: Int; } entity Bar extends Foo { } function main(): Int { return Bar{3i}.f; }', 'Expected "{" but got "extends" when parsing "type members"');
        parseTestFunctionInFileError('concept Foo { field f: Int; } entity Bar : Foo { } function main(): Int { return Bar{3i}.f; }', 'Expected "{" but got ":" when parsing "type members"'); 
    });
});



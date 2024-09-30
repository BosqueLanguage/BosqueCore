"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- entity decl inherits", () => {
    it("should check simple entity inherits fields", function () {
        checkTestFunctionInFile('concept Foo { field f: Int; } entity Bar provides Foo { } function main(): Int { return Bar{3i}.f; }'); 
        checkTestFunctionInFile('concept Foo { field f: Int; } entity Bar provides Foo { field g: Bool; } function main(): Bool { return Bar{3i, true}.g; }'); 
        checkTestFunctionInFile('concept Foo { field f: Int; } concept Baz { field g: Bool; } entity Bar provides Foo, Baz { } function main(): Int { return Bar{3i, true}.f; }'); 

        checkTestFunctionInFile('concept Foo<T> { field f: T; } entity Bar<T> provides Foo<T> { } function main(): Int { return Bar<Int>{3i}.f; }'); 
        checkTestFunctionInFile('concept Foo<U> { field f: U; } entity Bar<T> provides Foo<T> { } function main(): Int { return Bar<Int>{3i}.f; }'); 
    });

    it("should check fail simple entity inherits fields", function () {
        checkTestFunctionInFileError('concept Foo { field f: Int; } entity Bar provides Foo { } function main(): Int { return Bar{3n}.f; }', "Argument f expected type Int but got Nat");
        checkTestFunctionInFileError('concept Foo { field f: Int; } entity Bar provides Foo { } function main(): Nat { return Bar{3i}.f; }', "Expected a return value of type Nat but got Int"); 

        checkTestFunctionInFileError('concept Foo { field f: Int; } concept Baz { field g: Bool; } entity Bar provides Foo, Baz { } function main(): Int { return Bar{true, 3i}.f; }', "Argument f expected type Int but got Bool");
        checkTestFunctionInFileError('concept Foo { field f: Int; } concept Baz { field g: Bool; } entity Bar provides Foo, Baz { } function main(): Int { return Bar{3i, true}.h; }', "Could not find field h in type Bar"); 

        checkTestFunctionInFileError('concept Foo<T> { field f: T; } entity Bar<T> provides Foo<T> { } function main(): Nat { return Bar<Int>{3i}.f; }', "Expected a return value of type Nat but got Int"); 
        checkTestFunctionInFileError('concept Foo<U> { field f: U; } entity Bar<T> provides Foo<T> { } function main(): Int { return Bar<Int>{3n}.f; }', "Argument f expected type Int but got Nat"); 
    });

    it("should check fail template entity inherits fields", function () {
        checkTestFunctionInFileError('concept Foo<T> { field f: T; } entity Bar<T> provides Foo<T> { } function main(): Int { return Bar<Int>{3n}.f; }', "Argument f expected type Int but got Nat"); 
        checkTestFunctionInFileError('concept Foo<U> { field f: U; } entity Bar<T> provides Foo<T> { } function main(): Nat { return Bar<Int>{3i}.f; }', "Expected a return value of type Nat but got Int"); 
    });

    it("should check simple entity inherits fields and invariants", function () {
        checkTestFunctionInFile('concept Foo { field f: Int; invariant $f > 0i; } entity Bar provides Foo { } function main(): Int { return Bar{3i}.f; }');
        checkTestFunctionInFile('concept Foo { field f: Int; } entity Bar provides Foo { invariant $f > 0i; } function main(): Int { return Bar{3i}.f; }'); 

        checkTestFunctionInFile('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } function main(): Int { return Bar{3i}.f; }'); 
    });

    it("should check fail simple entity inherits fields and invariants", function () {
        checkTestFunctionInFileError('concept Foo { field f: Int; invariant $f > 0n; } entity Bar provides Foo { } function main(): Int { return Bar{3i}.f; }', "Operator > requires 2 arguments of the same type");
    });
});



"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity decl inherits", () => {
    it("should exec simple entity inherits fields", function () {
        runMainCode('concept Foo { field f: Int; } entity Bar provides Foo { } public function main(): Int { return Bar{3i}.f; }', "3i"); 
        runMainCode('concept Foo { field f: Int; } entity Bar provides Foo { field g: Bool; } public function main(): Bool { return Bar{3i, true}.g; }', "true"); 
        runMainCode('concept Foo { field f: Int; } concept Baz { field g: Bool; } entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i, true}.f; }', "3i"); 

        runMainCode('concept Foo<T> { field f: T; } entity Bar<T> provides Foo<T> { } public function main(): Int { return Bar<Int>{3i}.f; }', "3i"); 
        runMainCode('concept Foo<U> { field f: U; } entity Bar<T> provides Foo<T> { } public function main(): Int { return Bar<Int>{3i}.f; }', "3i"); 
    });

    it("should exec simple entity inherits fields and invariants", function () {
        runMainCode('concept Foo { field f: Int; invariant $f > 0i; } entity Bar provides Foo { } public function main(): Int { return Bar{3i}.f; }', "3i");
        runMainCode('concept Foo { field f: Int; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{3i}.f; }', "3i"); 

        runMainCode('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{3i}.f; }', "3i");  
    });

    it("should fail exec simple entity inherits fields and invariants", function () {
        runMainCodeError('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{0i}.f; }', "Error -- failed invariant @ test.bsq:3"); 
        runMainCodeError('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{-1i}.f; }', "Error -- failed invariant @ test.bsq:3"); 
    });
});

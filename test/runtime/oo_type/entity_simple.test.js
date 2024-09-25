"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity simple", () => {
    it("should exec simple entity", function () {
        runMainCode("entity Foo { field f: Int; } public function main(): Int { return Foo{3i}.f; }", [3n, "Int"]); 
        runMainCode("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{3i}.f; }", [3n, "Int"]); 
        runMainCode("entity Foo<T> { field f: T; } public function main(): Int { return Foo<Int>{3i}.f; }", [3n, "Int"]); 
    });

    it("should exec invariant fail simple entity", function () {
        runMainCodeError("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{-1i}.f; }", "Error -- failed invariant @ test.bsq:3"); 
    });
});

describe ("Exec -- entity simple with default fields", () => {
    it("should exec simple entity", function () {
        runMainCode("entity Foo { field f: Int = 3i; } public function main(): Int { return Foo{3i}.f; }", [3n, "Int"]); 

        runMainCode("entity Foo { field f: Int; field g: Int = $f; } public function main(): Int { return Foo{3i, 5i}.g; }", [5n, "Int"]); 
        runMainCode("entity Foo { field f: Int; field g: Int = $f; } public function main(): Int { return Foo{3i}.g; }", [3n, "Int"]); 
    });
});


"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity simple", () => {
    it("should exec simple entity", function () {
        runMainCode("entity Foo { field f: Int; } public function main(): Int { return Foo{3i}.f; }", "3i"); 
        runMainCode("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{3i}.f; }", "3i"); 
        runMainCode("entity Foo<T> { field f: T; } public function main(): Int { return Foo<Int>{3i}.f; }", "3i"); 
    });

    it("should exec invariant fail simple entity", function () {
        runMainCodeError("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{-1i}.f; }", "Error -- failed invariant @ test.bsq:3"); 
    });
});

describe ("Exec -- entity simple with default fields", () => {
    it("should exec simple entity", function () {
        runMainCode("entity Foo { field f: Int = 3i; } public function main(): Int { return Foo{3i}.f; }", "3i"); 

        runMainCode("entity Foo { field f: Int; field g: Int = $f; } public function main(): Int { return Foo{3i, 5i}.g; }", "5i"); 
        runMainCode("entity Foo { field f: Int; field g: Int = $f; } public function main(): Int { return Foo{3i}.g; }", "3i"); 
    });
});

describe ("Exec -- entity decl with consts", () => {
    it("should exec entity with consts", function () {
        runMainCode('entity Foo { const c: Int = 3i; } public function main(): Int { return Foo::c; }', "3i"); 
        runMainCode('entity Foo<T> { const c: Int = 3i; } public function main(): Int { return Foo<Nat>::c; }', "3i"); 
    });
});

describe ("Exec -- entity decl with functions", () => {
    it("should exec entity with functions", function () {
        runMainCode('entity Foo { function foo(): Int { return 3i; } } public function main(): Int { return Foo::foo(); }', "3i");

        runMainCode('entity Foo<T> { function foo(x: T): T { return x; } } public function main(): Int { return Foo<Int>::foo(3i); }', "3i");
        runMainCode('entity Foo { function foo<T>(x: T): T { return x; } } public function main(): Int { return Foo::foo<Int>(3i); }', "3i");
    });
});


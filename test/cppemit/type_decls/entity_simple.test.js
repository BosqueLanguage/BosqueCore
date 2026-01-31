"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- entity simple", () => {
    it("should emit simple entity", function () {
        checkTestEmitMainFunction("entity Foo { field f: Int; } public function main(): Foo { return Foo{3i}; }", "aaa"); 
        checkTestEmitMainFunction("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Foo { return Foo{3i}; }", "bbb"); 

        checkTestEmitMainFunction("entity Foo<T> { field f: T; } public function main(): Foo<Int> { return Foo<Int>{3i}; }", "ccc"); 
   
        checkTestEmitMainFunction("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Foo { return Foo{-1i}; }", "ccc"); 
    });
});

describe ("CPPEmit -- entity simple with default fields", () => {
    it("should emit simple entity", function () {
        checkTestEmitMainFunction("entity Foo { field f: Int = 3i; } public function main(): Foo { return Foo{3i}; }", "jjj"); 

        checkTestEmitMainFunction("entity Foo { field f: Int; field g: Int = $f; } public function main(): Foo { return Foo{3i, 5i}; }", "kkk"); 
        checkTestEmitMainFunction("entity Foo { field f: Int; field g: Int = $f; } public function main(): Foo { return Foo{3i}; }", "lll"); 
    });
});

describe ("CPPEmit -- entity decl with consts", () => {
    it("should emit entity with consts", function () {
        checkTestEmitMainFunction('entity Foo { const c: Int = 3i; } public function main(): Int { return Foo::c; }', "mmm"); 
        checkTestEmitMainFunction('entity Foo<T> { const c: Int = 3i; } public function main(): Int { return Foo<Nat>::c; }', "nnn"); 
    });
});

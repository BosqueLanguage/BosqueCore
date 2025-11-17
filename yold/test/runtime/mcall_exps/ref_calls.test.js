"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity ref methods", () => {
    it("should exec simple entity ref methods", function () {
        runMainCode('entity Foo { field f: Int; ref method foo(): Int { let b = this.f; ref this[f = 2i]; return b; }} public function main(): Int { var x = Foo{3i}; let b = ref x.foo(); return b + x.f; }', "5i"); 
    });
});

describe ("Exec -- eADT ref methods", () => {
    it("should exec simple eADT ref methods", function () {
        runMainCode('datatype Foo of | Foo1 { field f: Int; ref method foo(x: Int): Int { let b = this.f; ref this[f = 2i]; return b + x; }} ; public function main(): Int { var x = Foo1{3i}; return ref x.foo(1i); }', "4i"); 
    });
});

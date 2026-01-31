"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";
/*
describe ("CPPEmit -- Entity Constructor", () => {
    it("should emit positional", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; } public function main(): Int { return Foo{1i}.f; }', "1i");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{1i, false}.g; }', "false");
    });

    it("should emit nominal", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; } public function main(): Int { return Foo{f = 1i}.f; }', "1i");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{1i, g = true}.g; }', "true");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{f=1i, g = true}.g; }', "true");
    });

    it("should emit default", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int = 0i; } public function main(): Int { return Foo{}.f; }', "0i");
        checkTestEmitMainFunction('entity Foo { field f: Int = 0i; } public function main(): Int { return Foo{5i}.f; }', "5i");
    });
});

describe ("CPPEmit -- Entity w/ Invariant Constructor", () => {
    it("should emit positional", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; invariant $f > 3i; } public function main(): Int { return Foo{4i}.f; }', "4i");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } public function main(): Bool { return Foo{1i, false}.g; }', "false");

        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; invariant !$g; invariant $f != 0i; } public function main(): Bool { return Foo{1i, false}.g; }', "false");
    });

    it("should fail inv", function () {
        runMainCodeError("entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } public function main(): Bool { return Foo{1i, true}.g; }", "Error -- failed invariant @ test.bsq:3");
    });

    it("should exec default", function () {
        runMainCode('entity Foo { field f: Int = 0i; invariant $f != 3i; } public function main(): Int { return Foo{5i}.f; }', "5i");
    });
});
*/
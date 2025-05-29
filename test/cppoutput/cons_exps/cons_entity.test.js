"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Entity Constructor", () => {
    it("should exec positional", function () {
        runMainCode('entity Foo { field f: Int; } public function main(): Int { return Foo{1i}.f; }', "1_i");
        runMainCode('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{1i, false}.g; }', "false");
    });

    it("should exec nominal", function () {
        runMainCode('entity Foo { field f: Int; } public function main(): Int { return Foo{f = 1i}.f; }', "1_i");
        runMainCode('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{1i, g = true}.g; }', "true");
        runMainCode('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{f=1i, g = true}.g; }', "true");
    });

    it("should exec default", function () {
        runMainCode('entity Foo { field f: Int = 0i; } public function main(): Int { return Foo{}.f; }', "0_i");
        runMainCode('entity Foo { field f: Int = 0i; } public function main(): Int { return Foo{5i}.f; }', "5_i");
    });
});

/*
describe ("Exec -- Entity w/ Invariant Constructor", () => {
    it("should exec positional", function () {
        runMainCode('entity Foo { field f: Int; invariant $f > 3i; } public function main(): Int { return Foo{4i}.f; }', "4i");
        runMainCode('entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } public function main(): Bool { return Foo{1i, false}.g; }', "false");

        runMainCode('entity Foo { field f: Int; field g: Bool; invariant !$g; invariant $f != 0i; } public function main(): Bool { return Foo{1i, false}.g; }', "false");
    });

    it("should fail inv", function () {
        runMainCodeError("entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } public function main(): Bool { return Foo{1i, true}.g; }", "Error -- failed invariant @ test.bsq:3");
    });

    it("should exec default", function () {
        runMainCode('entity Foo { field f: Int = 0i; invariant $f != 3i; } public function main(): Int { return Foo{5i}.f; }', "5i");
    });
});
*/
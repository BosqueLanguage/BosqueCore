"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Entity Constructor", () => {
    it("should exec positional", function () {
        runishMainCodeUnsat('entity Foo { field f: Int; } public function main(): Int { return Foo{1i}.f; }', "(assert (not (= Main@main 1)))");
        runishMainCodeUnsat('entity Foo { field f: Int; field g: Bool; } public function main(k: Int): Bool { return Foo{k, true}.g; }', "(assert (not (Main@main 3)))");
        runishMainCodeUnsat('entity Foo { field f: Int; field g: Bool; } public function main(k: Int): Int { return Foo{k, true}.f; }', "(assert (not (= (Main@main 3) 3)))");
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

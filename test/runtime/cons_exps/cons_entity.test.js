"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- Entity Constructor", () => {
    it("should exec positional", function () {
        runMainCode('entity Foo { field f: Int; } public function main(): Int { return Foo{1i}.f; }', [1n, "Int"]);
        runMainCode('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{1i, false}.g; }', [false, "Bool"]);
    });

    it("should exec nominal", function () {
        runMainCode('entity Foo { field f: Int; } public function main(): Int { return Foo{f = 1i}.f; }', [1n, "Int"]);
        runMainCode('entity Foo { field f: Int; field g: Bool; } public function main(): Bool { return Foo{g = true, 1i}.g; }', [true, "Bool"]);
    });

    it("should exec default", function () {
        runMainCode('entity Foo { field f: Int = 0i; } public function main(): Int { return Foo{}.f; }', [0n, "Int"]);
        runMainCode('entity Foo { field f: Int = 0i; } public function main(): Int { return Foo{5i}.f; }', [5n, "Int"]);
    });
});

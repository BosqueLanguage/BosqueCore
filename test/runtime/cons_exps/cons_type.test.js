"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Type Alias Constructor", () => {
    it("should exec positional", function () {
        runMainCode('type Foo = Int; public function main(): Int { return Foo{1i}.value; }', [1n, "Int"]);
    });
});

describe ("Exec -- Type Alias w/ Invariant Constructor", () => {
    it("should exec positional", function () {
        runMainCode('type Foo = Int & { invariant $value > 3i; } public function main(): Int { return Foo{4i}.value; }', [4n, "Int"]);
    });

    it("should fail inv", function () {
        runMainCodeError("type Foo = Int & { invariant $value > 3i; } public function main(): Int { return Foo{1i}.value; }", "Error -- failed invariant @ test.bsq:3");
    });
});

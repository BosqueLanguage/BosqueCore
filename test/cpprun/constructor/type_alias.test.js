"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit-- Type Alias Constructor", () => {
    it("should emit simple type alias", function () {
        runTestSet('type Foo = Int; public function main(x: Int): Foo { return Foo{x}; }', [['0i', '0i<Main::Foo>'], ['+2i', '2i<Main::Foo>']], []);
    });
});

describe ("CPPexec-- Type Alias w/ Invariant Constructor", () => {
    it("should exec type alias with invariant", function () {
        runTestSet('type Foo = Int & { invariant $value > 3i; } public function main(x: Int): Foo { return Foo{x}; }', [['4i', '4i<Main::Foo>']], ['1i']);
    });
});

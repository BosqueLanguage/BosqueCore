"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit-- Type Alias Constructor", () => {
    it("should emit simple type alias", function () {
        runTestSet('type Foo = Int; public function main(): Foo { return Foo{1i}; }', [['xxxx', 'yyyy']], []);
    });
});

describe ("CPPexec-- Type Alias w/ Invariant Constructor", () => {
    it("should exec type alias with invariant", function () {
        runTestSet('type Foo = Int & { invariant $value > 3i; } public function main(): Foo { return Foo{4i}; }', [['xxxx', 'yyyy']], []);
    });
});

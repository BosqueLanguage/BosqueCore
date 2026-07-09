"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- basic greater", () => {
    it("should emit compare simple types", function () {
        checkTestEmitMainFunction("public function main(): Bool { return 0n > 1n; }", "Bool Mainᕒmain() { return 0_n > 1_n; }");
        checkTestEmitMainFunction("public function main(): Bool { return +2i > 2i; }", "Bool Mainᕒmain() { return 2_i > 2_i; }");
    });

    it("should emit compare type alias", function () {
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return 0i<Foo> > 1i<Foo>; }", "Bool Mainᕒmain() { return (MainᕒFoo{0_i}.value) > (MainᕒFoo{1_i}.value); }");
    });
});

describe ("CPPEmit -- basic greater or equal", () => {
    it("should emit compare simple types", function () {
        checkTestEmitMainFunction("public function main(): Bool { return 0n >= 1n; }", "Bool Mainᕒmain() { return 0_n >= 1_n; }");
        checkTestEmitMainFunction("public function main(): Bool { return +2i >= 2i; }", "Bool Mainᕒmain() { return 2_i >= 2_i; }");
    });

    it("should emit compare type alias", function () {
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return 0i<Foo> >= 1i<Foo>; }", "Bool Mainᕒmain() { return (MainᕒFoo{0_i}.value) >= (MainᕒFoo{1_i}.value); }");
    });
});

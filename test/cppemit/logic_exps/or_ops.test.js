"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- logical or", () => {
    it("should emit (simplify) simple or", function () {
        checkTestEmitMainFunction("public function main(): Bool { return true || false; }", "Bool Mainᕒmain() { return TRUE; }");
        checkTestEmitMainFunction("public function main(): Bool { return true || true; }", "Bool Mainᕒmain() { return TRUE; }");

        checkTestEmitMainFunction("const b: Bool = true; public function main(): Bool { return Main::b || true; }", "Bool Mainᕒmain() { return TRUE; }");
        checkTestEmitMainFunction("const b: Bool = true; public function main(): Bool { return Main::b || false; }", "Bool Mainᕒmain() { return TRUE; }");
        checkTestEmitMainFunction("type Foo = Bool; const b: Foo = true<Foo>; public function main(): Foo { return true<Foo> || Main::b; }", "MainᕒFoo Mainᕒmain() { return MainᕒFoo{(MainᕒFoo{TRUE}.value) | (MainᕒFoo{TRUE}.value)}; }");
    });

    it("should emit (no simplify) simple or", function () {
        checkTestEmitMainFunction("public function main(x: Bool): Bool { return x || x; }", "Bool Mainᕒmain(Bool x) { return x | x; }");
    });
});

"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- logical mixed", () => {
    it("should emit (simplify) simple mixed", function () {
        checkTestEmitMainFunction("public function main(): Bool { return true && !false; }", "Bool Mainᕒmain() { return TRUE; }");

        checkTestEmitMainFunction("const b: Bool = true; public function main(): Bool { return !Main::b; }", "Bool Mainᕒmain() { return FALSE; }");

        checkTestEmitMainFunction("type Foo = Bool; const b: Foo = true<Foo>; public function main(x: Foo): Foo { let z = true<Foo>; return z && x || Main::b; }", "MainᕒFoo Mainᕒmain(MainᕒFoo x) { MainᕒFoo z = MainᕒFoo{TRUE}; return MainᕒFoo{((MainᕒFoo{((z.value) & (x.value))}).value) | (MainᕒFoo{TRUE}.value)}; }");
        checkTestEmitMainFunction("type Foo = Bool; const b: Foo = true<Foo>; public function main(x: Foo): Foo { let z = true<Foo>; return z && x || !x; }", "MainᕒFoo Mainᕒmain(MainᕒFoo x) { MainᕒFoo z = MainᕒFoo{TRUE}; return MainᕒFoo{((MainᕒFoo{((z.value) & (x.value))}).value) | ((MainᕒFoo{(!(x.value))}).value)}; }");
    });

    it("should emit (no simplify) simple mixed", function () {
        checkTestEmitMainFunction("public function main(x: Bool): Bool { let y = x; return x && y || !x; }", "Bool Mainᕒmain(Bool x) { Bool y = x; return (x & y) | (!x); }");
        checkTestEmitMainFunction("public function main(x: Bool): Bool { let y = x; return !x && y || x; }", "Bool Mainᕒmain(Bool x) { Bool y = x; return ((!x) & y) | x; }");
    });
});

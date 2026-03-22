"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- access field", () => {
    it("should emit simple field access", function () {
        checkTestEmitMainFunction("entity Foo { field f: Int; } public function main(x: Foo): Int { return x.f; }", "Int Mainᕒmain(MainᕒFoo x) { return x.f; }");
        checkTestEmitMainFunction("entity Foo { field f: Int; } public function foo(): Foo { return Foo{1i}; } public function main(): Int { return foo().f; }", "Int Mainᕒmain() { MainᕒFoo tmp_0 = Mainᕒfoo(); return tmp_0.f; }");

        checkTestEmitMainFunction("entity Foo { field f: Int; field g: Nat; } public function main(x: Foo): Nat { return x.g; }", "Nat Mainᕒmain(MainᕒFoo x) { return x.g; }");
        checkTestEmitMainFunction("entity Bar { field h: Bool; } entity Foo { field f: Bar; } public function main(x: Foo): Bool { return x.f.h; }", "Bool Mainᕒmain(MainᕒFoo x) { return x.f.h; }");
    });

    it("should emit inherited field access", function () {
        checkTestEmitMainFunction("concept Baz { field h: Bool; } entity Foo provides Baz { field f: Int; } public function main(x: Foo): Int { return x.f; }", "Int Mainᕒmain(MainᕒFoo x) { return x.f; }");
        checkTestEmitMainFunction("concept Baz { field h: Bool; } entity Foo provides Baz { field f: Int; } public function main(x: Foo): Bool { return x.h; }", "Bool Mainᕒmain(MainᕒFoo x) { return x.h; }");

        checkTestEmitMainFunction("concept Baz { field h: Bool; field y: Int; } entity Foo provides Baz { field f: Int; } public function main(x: Baz): Int { return x.y; }", "Int Mainᕒmain(MainᕒBaz x) { return x.accessfield<Int, 1>(); }");
        checkTestEmitMainFunction("concept Baz { field h: Bool; } entity Foo provides Baz { field f: Int; } public function main(x: Baz): Bool { return x.h; }", "Bool Mainᕒmain(MainᕒBaz x) { return x.accessfield<Bool, 0>(); }");

        checkTestEmitMainFunction("entity FIn { field f: Int; } concept Bar { field h: FIn; } entity Foo provides Bar { field f: Bool; } public function main(x: Foo): Bool { return x.f; }", "Bool Mainᕒmain(MainᕒFoo x) { return x.f; }");
        checkTestEmitMainFunction("entity FIn { field f: Int; } concept Bar { field h: FIn; } entity Foo provides Bar { field f: Bool; } public function main(x: Foo): Int { return x.h.f; }", "Int Mainᕒmain(MainᕒFoo x) { return x.h.f; }");

        checkTestEmitMainFunction("entity FIn { field f: Int; } concept Bar { field h: FIn; } entity Foo provides Bar { field f: Bool; } public function main(x: Bar): Int { return x.h.f; }", "Int Mainᕒmain(MainᕒBar x) { return x.accessfield<MainᕒFIn, 0>().f; }");
    });
});

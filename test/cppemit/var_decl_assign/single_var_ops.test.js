"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- simple declare only", () => {
    it("should emit simple declares", function () {
        checkTestEmitMainFunction("public function main(): Int { var x: Int; return 0i; }", "Int Mainᕒmain() { Int x; return 0_i; }");
        checkTestEmitMainFunction("public function main(): Bool { var x: Bool; return true; }", "Bool Mainᕒmain() { Bool x; return TRUE; }");
    });
});

describe ("CPPEmit -- simple declare-assign only", () => {
    it("should emit simple declare-assign", function () {
        checkTestEmitMainFunction("public function main(): Int { var x: Int = 5i; return x; }", "Int Mainᕒmain() { Int x = 5_i; return x; }");
        checkTestEmitMainFunction("public function main(): Int { ref x: Int = 5i; return x; }", "Int Mainᕒmain() { Int x = 5_i; return x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Bool = true; return x; }", "Bool Mainᕒmain() { Bool x = TRUE; return x; }");
    });

    it("should emit simple declare-assign infer type", function () {
        checkTestEmitMainFunction("public function main(): Int { var x = 5i; return x; }", "Int Mainᕒmain() { Int x = 5_i; return x; }");
        checkTestEmitMainFunction("public function main(): Int { ref x = 5i; return x; }", "Int Mainᕒmain() { Int x = 5_i; return x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x = true; return x; }", "Bool Mainᕒmain() { Bool x = TRUE; return x; }");
    });

    it("should emit simple declare-assign with coerce", function () {
        checkTestEmitMainFunction('public function main(): Option<Int> { let x: Option<Int> = none; return x; }', "OptionᐸIntᐳ Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::none; return x; }");
        checkTestEmitMainFunction('public function main(): Option<Int> { let x: Option<Int> = some(3i); return x; }', "OptionᐸIntᐳ Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; return x; }");
        checkTestEmitMainFunction('public function main(): Option<Int> { ref x: Option<Int> = some(3i); return x; }', "OptionᐸIntᐳ Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; return x; }");

        checkTestEmitMainFunction('concept Baz {} entity Foo provides Baz {} public function main(): Baz { let x: Baz = Foo{}; return x; }', "MainᕒBaz Mainᕒmain() { MainᕒBaz x = MainᕒBaz{MainᕒFoo{}}; return x; }");
        checkTestEmitMainFunction('concept Baz {} entity Foo provides Baz {} public function main(): Baz { var x: Baz = Foo{}; return x; }', "MainᕒBaz Mainᕒmain() { MainᕒBaz x = MainᕒBaz{MainᕒFoo{}}; return x; }");
    });
});

describe ("CPPEmit -- simple assign", () => {
    it("should emit simple assign", function () {
        checkTestEmitMainFunction("public function main(): Int { var x: Int = 5i; x = 2i; return x; }", "Int Mainᕒmain() { Int x = 5_i; x = 2_i; return x; }");
        checkTestEmitMainFunction("public function main(): Int { var x: Int = 5i; x = 2i; x = 0i; return x; }", "Int Mainᕒmain() { Int x = 5_i; x = 2_i; x = 0_i; return x; }");
    });

    it("should ignore assign", function () {
        checkTestEmitMainFunction("public function main(): Int { _ = 2i; return 0i; }", "Int Mainᕒmain() { return 0_i; }");
        checkTestEmitMainFunction("entity Foo {} public function main(): Int { _ = Foo{}; return 0i; }", "Int Mainᕒmain() { return 0_i; }");
    });

    it("should emit simple assign with coerce", function () {
        checkTestEmitMainFunction('public function main(): Option<Int> { var x: Option<Int> = none; x = some(3i); return x; }', "OptionᐸIntᐳ Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::none; x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; return x; }");
        checkTestEmitMainFunction('concept Baz {} entity Foo provides Baz {} public function main(): Baz { var x: Baz = Foo{}; x = Foo{}; return x; }', "MainᕒBaz Mainᕒmain() { MainᕒBaz x = MainᕒBaz{MainᕒFoo{}}; x = MainᕒBaz{MainᕒFoo{}}; return x; }");
    });
});

describe ("CPPEmit -- declare-assign with refs", () => {
    it("should emit declare-assign with refs", function () {
        checkTestEmitMainFunction("function foo(out y: Int): Int { return 1i; } public function main(): Int { var y: Int; let x = foo(out y); return x; }", "Int Mainᕒmain() { Int y; Int x = Mainᕒfooᙾref(y); return x; }");
        checkTestEmitMainFunction("entity Foo { ref method foo(): Int { return 1i; } } public function main(): Int { ref z = Foo{}; let x = ref z.foo(); return x; }", "Int Mainᕒmain() { MainᕒFoo z = MainᕒFoo{}; Int x = MainᕒFooᑀfooᙾref(z); return x; }");
    });
});

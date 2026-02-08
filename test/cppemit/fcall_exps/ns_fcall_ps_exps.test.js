"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CppEmit -- NamespaceFunction Ref Params", () => {
    it("should emit simple ref", function () {
        checkTestEmitMainFunction('function foo(out y: Int): Int { y = 2i; return 1i; } public function main(): Int { var i = 0i; return foo(out i); }', "Int Mainᕒmain() { Int i = 0_i; Int tmp_0 = Mainᕒfooᙾref(i); return tmp_0; }");
        checkTestEmitMainFunction('function foo(out? y: Int): Bool { y = 2i; return true; } public function main(): Bool { var i = 0i; return foo(out? i); }', "Bool Mainᕒmain() { Int i = 0_i; Bool tmp_0 = Mainᕒfooᙾref(i); return tmp_0; }");
        checkTestEmitMainFunction('function foo(inout y: Int): Int { y = y + 2i; return 1i; } public function main(): Int { var i = 0i; return foo(inout i); }', "Int Mainᕒmain() { Int i = 0_i; Int tmp_0 = Mainᕒfooᙾref(i); return tmp_0; }");
        checkTestEmitMainFunction('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } public function main(): Int { ref ff = Foo{}; return foo(ref ff); }', "Int Mainᕒmain() { MainᕒFoo ff = MainᕒFoo{}; Int tmp_0 = Mainᕒfooᙾref(ff); return tmp_0; }");     
    });

    it("should emit staged ref", function () {
        checkTestEmitMainFunction('function foo(out y: Int): Int { y = 2i; return 1i; } public function main(): Int { var i = 0i; let z = foo(out i); return z; }', "Int Mainᕒmain() { Int i = 0_i; Int z = Mainᕒfooᙾref(i); return z; }");
        checkTestEmitMainFunction('function foo(out y: Int): Int { y = 2i; return 1i; } public function main(): Int { var i = 0i; i = foo(out i); return i; }', "Int Mainᕒmain() { Int i = 0_i; i = Mainᕒfooᙾref(i); return i; }");
        checkTestEmitMainFunction('function foo(inout y: Int): Int { y = y + 2i; return 1i; } public function main(): Int { var i = 0i; i = foo(inout i); return i; }', "Int Mainᕒmain() { Int i = 0_i; i = Mainᕒfooᙾref(i); return i; }");
        checkTestEmitMainFunction('entity Foo{ } function foo(ref y: Foo) { return; } public function main(): Foo { ref ff = Foo{}; foo(ref ff); return ff; }', "ddd");     
        checkTestEmitMainFunction('function foo(out y: Int): Int { y = 2i; return 1i; } public function main(): Int { var i = 0i; let x = foo(out i); return x + i; }', "ppp");
    });

    it("should emit simple out?", function () {
        checkTestEmitMainFunction('function foo(out? y: Int): Bool { y = 2i; return true; } public function main(): Int { var i: Int; if(foo(out? i)) { return i; } return 0i; }', "Int Mainᕒmain() { Int i; Bool tmp_0 = Mainᕒfooᙾref(i); if(tmp_0) { return i; } return 0_i; }");
    });
});

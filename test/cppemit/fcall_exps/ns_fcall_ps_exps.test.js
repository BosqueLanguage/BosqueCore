"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CppEmit -- NamespaceFunction Ref Params", () => {
    it("should emit simple ref", function () {
        checkTestEmitMainFunction('public function foo(out y: Int): Int { y = 2i; return 1i; } function main(): Int { var i = 0i; return foo(out i); }', "aaaa");
        checkTestEmitMainFunction('public function foo(out? y: Int): Bool { y = 2i; return true; } function main(): Bool { var i = 0i; return foo(out? i); }', "bbb");
        checkTestEmitMainFunction('public function foo(inout y: Int): Int { y = y + 2i; return 1i; } function main(): Int { var i = 0i; return foo(inout i); }', "ccc");
        checkTestEmitMainFunction('entity Foo{ } public function foo(ref y: Foo): Int { return 1i; } function main(): Int { ref ff = Foo{}; return foo(ref ff); }', "ddd");     
    });

    it("should emit simple ref", function () {
        checkTestEmitMainFunction('public function foo(out y: Int): Int { y = 2i; return 1i; } function main(): Int { var i = 0i; let z = foo(out i); return z; }', "aaaa");
        checkTestEmitMainFunction('public function foo(out y: Int): Int { y = 2i; return 1i; } function main(): Int { var i = 0i; i = foo(out? i) return i; }', "bbb");
        checkTestEmitMainFunction('public function foo(inout y: Int): Int { y = y + 2i; return 1i; } function main(): Int { var i = 0i; return foo(inout i) return i; }', "ccc");
        checkTestEmitMainFunction('entity Foo{ } public function foo(ref y: Foo): Int { return 1i; } function main(): Int { ref ff = Foo{}; return foo(ref ff); }', "ddd");     
    });

    it("should emit simple out?", function () {
        checkTestEmitMainFunction('public function foo(out? y: Int): Bool { y = 2i; return true; } function main(): Bool { var i; if(foo(out? i)) { return i; } return 0i; }', "bbb");
    });
});

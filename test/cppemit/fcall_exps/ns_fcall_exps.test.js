"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- NamespaceFunction (no template)", () => {
    it("should emit simple positional", function () {
        checkTestEmitMainFunction("function foo(): Int { return 1i; } public function main(): Int { return foo(); }", "Int Mainᕒmain() { return Mainᕒfoo(); }");
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, true); }", "Int Mainᕒmain() { return Mainᕒfoo(1_i, TRUE); }");
    });

    it("should emit simple named", function () {
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(x=1i, y=true); }", "Int Mainᕒmain() { return Mainᕒfoo(1_i, TRUE); }");
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "Int Mainᕒmain() { return Mainᕒfoo(1_i, TRUE); }");
    });

    it("should emit simple mixed", function () {
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, y=true); }", "Int Mainᕒmain() { return Mainᕒfoo(1_i, TRUE); }");
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "Int Mainᕒmain() { return Mainᕒfoo(1_i, TRUE); }");
    });

    it("should emit skip positions", function () {
        checkTestEmitMainFunction('function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, _, y = true); }', "Int Mainᕒmain() { return Mainᕒfoo(1_i, TRUE); }");
        checkTestEmitMainFunction('function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(_, false, x = 1i); }', "Int Mainᕒmain() { return Mainᕒfoo(1_i, FALSE); }");
    });

    it("should emit simple default", function () {
        checkTestEmitMainFunction("function foo(x: Int, y: Int = 3i): Int { return x + y; } public function main(): Int { return foo(1i, 2i); }", "Int Mainᕒmain() { return Mainᕒfoo(1_i, 2_i); }");
        checkTestEmitMainFunction("function foo(x: Int, y: Int = 1i): Int { return x + y; } public function main(): Int { return foo(1i); }", "Int Mainᕒmain() { return Mainᕒfoo(1_i, 1_i); }");
    });

    it("should emit simple rest", function () {
        checkTestEmitMainFunction('function foo(x: Int, ...y: List<Int>): Int { return x; } public function main(): Int { return foo(1i); }', "xxxx");
        checkTestEmitMainFunction('function foo(x: Int, ...y: List<Int>): Int { return x; } public function main(): Int { return foo(1i, 2i); }', "yyyy");
        checkTestEmitMainFunction('function foo(x: Int, ...y: List<Int>): Int { return x; } public function main(): Int { return foo(1i, 2i, 3i); }', "zzzz");

        checkTestEmitMainFunction('function foo(x: Int, ...y: List<Int>): Int { return x; } public function main(): Int { return foo(x = 0i, 2i, 3i); }', "qqq");
    });
});

describe ("CPPEmit -- NamespaceFunction (with template)", () => {
    it("should emit simple positional", function () {
        checkTestEmitMainFunction("function foo<T>(x: T): T { return x; } public function main(): Int { return foo<Int>(3i); }", "Int Mainᕒmain() { return MainᕒfooᐸIntᐳ(3_i); }");
    });
});

"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- NamespaceFunction (no template)", () => {
    it("should emit simple positional", function () {
        checkTestEmitMainFunction("function foo(): Int { return 1i; } public function main(): Int { return foo(); }", "aaa");
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, true); }", "bbb");
    });

    it("should emit simple named", function () {
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(x=1i, y=true); }", "ccc");
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "ddd");
    });

    it("should emit simple mixed", function () {
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, y=true); }", "eee");
        checkTestEmitMainFunction("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "fff");
    });

    it("should emit skip positions", function () {
        checkTestEmitMainFunction('function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, _, y = true); }', "ggg");
        checkTestEmitMainFunction('function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(_, false, x = 1i); }', "hhh");
    });

    it("should emit simple default", function () {
        checkTestEmitMainFunction("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i, 2i); }", "iii");
        checkTestEmitMainFunction("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i); }", "jjj");
    });

    it.todo("should emit simple rest", function () {
    });
});

describe ("CPPEmit -- NamespaceFunction (with template)", () => {
    it("should emit simple positional", function () {
        checkTestEmitMainFunction("function foo<T>(x: T): T { return x; } public function main(): Int { return foo<Int>(3i); }", "kkk");
    });
});

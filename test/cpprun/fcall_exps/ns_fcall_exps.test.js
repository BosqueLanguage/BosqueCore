"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- NamespaceFunction (no template)", () => {
    it("should exec simple positional", function () {
        runTestSet("function foo(): Int { return 1i; } public function main(v: Int): Int { return foo(); }", [['1i', '1i']], []);
        runTestSet("function foo(x: Int, y: Bool): Int { return x; } public function main(v: Int): Int { return foo(x=v, y=true); }", [['2i', '2i']], []);
    });

    it("should exec simple named", function () {
        runTestSet("function foo(x: Int, y: Bool): Int { return x; } public function main(v: Int): Int { return foo(x=v, y=true); }", [['2i', '2i']], []);
        runTestSet("function foo(x: Int, y: Bool): Int { return x; } public function main(v: Int): Int { return foo(y=true, x=v); }", [['3i', '3i']], []);
    });

    it("should exec simple mixed", function () {
        runTestSet("function foo(x: Int, y: Bool): Int { return x; } public function main(v: Int): Int { return foo(v, y=true); }", [['4i', '4i']], []);
        runTestSet("function foo(x: Int, y: Bool): Int { return x; } public function main(v: Int): Int { return foo(y=true, x=v); }", [['5i', '5i']], []);
    });

    it("should exec skip positions", function () {
        runTestSet('function foo(x: Int, y: Bool): Int { return x; } public function main(v: Int): Int { return foo(v, _, y = true); }', [['6i', '6i']], []);
        runTestSet('function foo(x: Int, y: Bool): Int { return x; } public function main(v: Int): Int { return foo(_, false, x = v); }', [['7i', '7i']], []);
    });

    it("should exec simple default", function () {
        runTestSet("function foo(x: Int, y: Int = 3i): Int { return x + y; } public function main(v: Int): Int { return foo(1i, 2i); }", [['3i', '3i']], []);
        runTestSet("function foo(x: Int, y: Int = 1i): Int { return x + y; } public function main(v: Int): Int { return foo(1i); }", [['2i', '2i']], []);
    });

    it.todo("should exec simple rest", function () {
    });
});

describe ("CPPExec -- NamespaceFunction (with template)", () => {
    it("should exec simple positional", function () {
        runTestSet("function foo<T>(x: T): T { return x; } public function main(v: Int): Int { return foo<Int>(v); }", [['0i', '0i'], ['9i', '9i']], []);
    });
});

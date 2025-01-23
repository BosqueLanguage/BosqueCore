"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- NamespaceFunction (no template)", () => {
    it("should exec simple positional", function () {
        runMainCode("function foo(): Int { return 1i; } public function main(): Int { return foo(); }", "1i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, true); }", "1i");
    });

    it("should exec simple named", function () {
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(x=1i, y=true); }", "1i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "1i");
    });

    it("should exec simple mixed", function () {
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(x=1i, true); }", "1i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, 1i); }", "1i");
    });

    it("should exec simple default", function () {
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i, 2i); }", "3i");
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i); }", "2i");
    });
});

describe ("Exec -- NamespaceFunction (with template)", () => {
    it("should exec simple positional", function () {
        runMainCode("function foo<T>(x: T): T { return x; } public function main(): Int { return foo<Int>(1i); }", "1i");
    });

    it("should exec two instantiations", function () {
        runMainCode("function foo<T>(x: T): T { return x; } public function main(): Int { if(foo<Nat>(1n) > 0n) { return foo<Int>(1i); } return 0i; }", "1i");
    });
});

"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- NamespaceFunction (no template)", () => {
    it("should exec simple positional", function () {
        runMainCode("function foo(): Int { return 1i; } public function main(): Int { return foo(); }", "1_i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, true); }", "1_i");
    });

/*  Enable when default val support in explicitify
    it("should exec simple named", function () {
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(x=1i, y=true); }", "1_i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "1_i");
    });
*/
/*  Enable when default val support in explicitify
    it("should exec simple mixed", function () {
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, y=true); }", "1_i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "1_i");
    });
*/
/*  Enable when default val support in explicitify
    it("should exec simple default", function () {
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i, 2i); }", "3_i");
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i); }", "2_i");
    });
*/
});

describe ("CPP Emit Evaluate -- NamespaceFunction (with template)", () => {
    it("should exec simple positional", function () {
        runMainCode("function foo<T>(x: T): T { return x; } public function main(): Int { return foo<Int>(1i); }", "1_i");
    });

    it("should exec two instantiations", function () {
        runMainCode("function foo<T>(x: T): T { return x; } public function main(): Int { if(foo<Nat>(1n) > 0n) { return foo<Int>(1i); } return 0i; }", "1_i");
    });
});

describe ("CPP Emit Evaluate -- NamespaceFunction with builtin", () => {
    it("should exec simple float builtin", function () {
        runMainCode("function sqrt(x: Float): Float { return Float::sqrt(x); } public function main(): Bool { return sqrt(5.0f) < 3.0f; }", "true");
        runMainCode("function square(x: Float): Float { return Float::square(x); } public function main(): Bool { return square(5.0f) > 20.0f; }", "true");
    });
});
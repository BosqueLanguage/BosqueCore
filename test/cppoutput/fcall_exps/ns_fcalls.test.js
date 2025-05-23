"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("Exec -- NamespaceFunction (no template)", () => {
    it("should exec simple positional", function () {
        runMainCode("function foo(): Int { return 1i; } public function main(): Int { return foo(); }", "1_i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, true); }", "1_i");
    });

    /*
    it("should exec simple named", function () {
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(x=1i, y=true); }", "1_i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "1_i");
    });

    it("should exec simple mixed", function () {
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, y=true); }", "1_i");
        runMainCode("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "1_i");
    });

    it("should exec simple default", function () {
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i, 2i); }", "3_i");
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i); }", "2_i");
    });
    */
});
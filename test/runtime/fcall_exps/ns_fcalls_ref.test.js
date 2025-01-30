"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- NamespaceFunction Ref Params", () => {
    it("should exec simple ref", function () {
        runMainCode('entity Foo{ field x: Int; } function foo(ref y: Foo): Int { return 1i; } public function main(): Int { var ff = Foo{0i}; let a = foo(ref ff); return a; }', "1i"); 
        runMainCode('entity Foo{ field x: Int; } function foo(ref y: Foo): Int { ref y[x = 2i]; return 1i; } public function main(): Int { var ff = Foo{0i}; let a = foo(ref ff); return ff.x; }', "2i"); 
    });

    it("should exec direct return ref", function () {
        runMainCode('entity Foo{ field x: Int; } function foo(ref y: Foo): Int { return bar(ref y); } function bar(ref z: Foo): Int { ref z[x = 2i]; return 1i; } public function main(): Int { var ff = Foo{0i}; let a = foo(ref ff); return a; }', "1i"); 
        runMainCode('entity Foo{ field x: Int; } function foo(ref y: Foo): Int { return bar(ref y); } function bar(ref z: Foo): Int { ref z[x = 2i]; return 1i; } public function main(): Int { var ff = Foo{0i}; let a = foo(ref ff); return ff.x; }', "2i"); 
    });
});


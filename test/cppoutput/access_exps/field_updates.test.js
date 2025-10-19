"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- simple field updates", () => {
    it("should exec simple field updates", function () {
        runMainCode('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; return v[x = 2i].x; }', "2_i");
        runMainCode('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; return v[x = $x + 1i].x; }', "2_i");
    });

    it("should exec postfix field updates", function () {
        runMainCode('entity Foo { field x: Int; field y: Int; } entity Bar { field f: Foo; } public function main(): Int { let a = Bar{Foo{1i, 0i}}; let b = a.f[x=3i]; return b.x; }', "3_i");
    });
});

"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- simple ref updates", () => {
    it("should exec simple ref updates", function () {
        runMainCode('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; ref v[x = 2i]; return v.x; }', "2i");
        runMainCode('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; ref v[x = $x + 1i]; return v.x; }', "2i");
    });
});


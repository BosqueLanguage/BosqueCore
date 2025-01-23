"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- elist return", () => {
    it("should exec elist returns", function () {
        runMainCode('function foo(): (|Int, Bool|) { return (|2i, false|); } public function main(): Int { return foo().0; }', "2i");
        runMainCode('function foo(): (|Int, Bool|) { return 2i, false; } public function main(): Int { return foo().0; }', "2i");
    });

    it("should exec elist returns w/ convert", function () {
        runMainCode('function foo(): (|Option<Int>, Bool|) { return (|some(2i), false|); } public function main(): Int { return foo().0@some; }', "2i");
        runMainCode('function foo(): (|Option<Int>, Bool|) { return some(2i), false; } public function main(): Int { return foo().0@some; }', "2i");
    });
});

"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- switch Statement", () => {
    it("should exec simple switch", function () {
        runMainCode("public function main(): Int { let x = 3i; switch(x) { 0i => { return 0i; } | _ => { return 1i; } } }", "1i");
        runMainCode("public function main(): Int { let x = 0i; switch(x) { 0i => { return 0i; } | _ => { return 1i; } } }", "0i");
    });

    it("should exec fail simple switch", function () {
        runMainCodeError("public function main(): Int { let x = 3i; switch(x) { 0i => { return 0i; } | 1i => { return 1i; } } }", 'Error -- exhaustive switch @ test.bsq:3');
    });

    it("should exec enum switch", function () {
        runMainCode("enum Foo { f, g } public function main(): Int { let x = Foo#f; switch(x) { Foo#f => { return 0i; } | _ => { return 1i; } } }", "0i");
        runMainCode("enum Foo { f, g } public function main(): Int { let x = Foo#f; switch(x) { Foo#f => { return 0i; } | Foo#g => { return 1i; } } }", "0i");
        runMainCode("enum Foo { f, g } public function main(): Int { let x = Foo#g; switch(x) { Foo#f => { return 0i; } | Foo#g => { return 1i; } } }", "1i");
    });
});

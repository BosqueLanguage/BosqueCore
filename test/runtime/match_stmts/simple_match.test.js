"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- match Statement", () => {
    it("should exec simple match", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); match(x) { | None => { return 0i; } | _ => { return 1i; } } }", "1i");
        runMainCode("public function main(): Int { let x: Option<Int> = none; match(x) { | None => { return 0i; } | _ => { return 1i; } } }", "0i");
        
        runMainCode("datatype Foo of | F1 {} | F2 {}; public function main(): Int { let x: Foo = F1{}; match(x) { | F1 => { return 0i; } | F2 => { return 1i; } } }", "0i");
    });

    it("should exec fail simple match", function () {
        runMainCodeError("datatype Foo of | F1 {} | F2 {} | F3 {}; public function main(): Int { let x: Foo = F3{}; match(x) { | F1 => { return 0i; } | F2 => { return 1i; } } }", 'Error -- exhaustive switch @ test.bsq:3');
    });

    it("should exec binder match", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); match(x)@ { | None => { return 0i; } | _ => { return 1i; } } }", "1i");
        
        runMainCode("datatype Foo of | F1 {} | F2 { g: Int }; public function main(): Int { let x: Foo = F1{}; match(x)@ { | F1 => { return 0i; } | F2 => { return $x.g; } } }", "0i");
        runMainCode("datatype Foo of | F1 {} | F2 { g: Int }; public function main(): Int { let x: Foo = F2{5i}; match(x)@ { | F1 => { return 0i; } | F2 => { return $x.g; } } }", "5i");
    });
});

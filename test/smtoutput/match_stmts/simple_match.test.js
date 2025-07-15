"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- match Statement", () => {
    it("should smt exec simple match", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); match(x) { None => { return 0i; } | _ => { return 1i; } } }", "(assert (not (= 1 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = none; match(x) { None => { return 0i; } | _ => { return 1i; } } }", "(assert (not (= 0 Main@main)))");

        runishMainCodeUnsat("datatype Foo of F1 {} | F2 {}; public function main(): Int { let x: Foo = F1{}; match(x) { F1 => { return 0i; } | F2 => { return 1i; } } }", "(assert (not (= 0 Main@main)))");
    });

    it("should smt exec fail simple match", function () {
        runishMainCodeUnsat("datatype Foo of F1 {} | F2 {} | F3 {}; public function main(): Int { let x: Foo = F3{}; match(x) { F1 => { return 0i; } | F2 => { return 1i; } } }", '(assert (not (is-@Result-err Main@main)))');
    });

    it("should smt exec binder match", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); match(x)@ { None => { return 0i; } | _ => { return 1i; } } }", "(assert (not (= 1 Main@main)))");

        runishMainCodeUnsat("datatype Foo of F1 {} | F2 { g: Int }; public function main(): Int { let x: Foo = F1{}; match(x)@ { F1 => { return 0i; } | F2 => { return $x.g; } } }", "(assert (not (= 0 Main@main)))");
        runishMainCodeUnsat("datatype Foo of F1 {} | F2 { g: Int }; public function main(): Int { let x: Foo = F2{5i}; match(x)@ { F1 => { return 0i; } | F2 => { return $x.g; } } }", "(assert (not (= 5 Main@main)))");
    });
});

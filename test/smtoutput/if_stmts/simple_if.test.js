"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- If Statement", () => {
    it("should SMT exec simple ifs", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { if(x != 0i) { return 3i; } return 1i; }", "(assert (not (= 3 (Main@main 3))))");
        runishMainCodeUnsat("public function main(x: Int): Int { if(x != 0i) { return 3i; } return 1i; }", "(assert (not (= 1 (Main@main 0))))");

        runishMainCodeUnsat("public function main(x: Int): Int { if(x != 0i) { return 6i // 2i; } return 1i; }", "(assert (not (= (@Result-ok 3) (Main@main 3))))");
        runishMainCodeUnsat("public function main(x: Int): Int { if(x != 0i) { return 3i; } return 2i // 2i; }", "(assert (not (= (@Result-ok 3) (Main@main 3))))");

        runishMainCodeUnsat("public function main(x: Int): Int { if(x // 2i != 0i) { return 3i; } return 1i; }", "(assert (not (= (@Result-ok 3) (Main@main 6))))");
        runishMainCodeUnsat("public function main(x: Int): Int { if(x // 2i != 0i) { return 6i // 2i; } return 1i; }", "(assert (not (= (@Result-ok 3) (Main@main 6))))");

        runishMainCodeUnsat("public function main(x: Int): Int { if(x // 2i != 0i // 2i) { return 6i // 2i; } return 1i; }", "(assert (not (= (@Result-ok 3) (Main@main 6))))");
    });

    it("should smt check simple simple", function () {
        checkProperties("public function main(): Int { if(true) { return 2i; } return 3i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Int 2 )" }]);
        checkProperties("public function main(): Int { if(false) { return 2i; } return 3i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Int 3 )" }]);
    });

    it("should SMT exec itest ifs", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } return 1i; }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = none; if(x)some { return 3i; } return 1i; }", "(assert (not (= 1 Main@main)))");
    });

    it("should SMT exec binder itest ifs", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $x; } return 1i; }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); if($y = x)@some { return $y; } return 1i; }", "(assert (not (= 3 Main@main)))");
    });

    it("should SMT exec follow ifs", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { var y: Int = 0i; if(x != 0i) { y = 1i; } return y + 1i; }", "(assert (not (= 2 (Main@main 3))))");
    });

    /*
    it("should SMT exec binder & reflow itest ifs", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); if(x)@@!some { return 0i; } return x; }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = none; if(x)@@!some { return 0i; } return x; }", "(assert (not (= 0 Main@main)))");
    });
    */
});


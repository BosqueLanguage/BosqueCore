"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT exec -- Simple if-expression", () => {
    it("should SMT exec simple refine", function () {
        runishMainCodeUnsat("public function main(): Int { return if(true) then 2i else 3i; }", "(assert (not (= 2 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { return if(false) then 2i else 3i; }", "(assert (not (= 3 Main@main)))");
    });

    it("should smt check simple simple", function () {
        checkProperties("public function main(): Int { return if(true) then 2i else 3i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Int 2 )" }]);
        checkProperties("public function main(): Int { return if(false) then 2i else 3i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Int 3 )" }]);
    });

    it("should SMT exec simple", function () {
        runishMainCodeUnsat("public function main(): Int { return if(1i != 2i) then 2i else 3i; }", "(assert (not (= 2 Main@main)))");
        runishMainCodeUnsat("public function main(): Int { return if(1i == 2i) then 2i else 3i; }", "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat("public function main(x: Int): Int { return if(x > 0i) then x else (5i // 0i); }", "(assert (not (= (@Result-ok 3) (Main@main 3))))");
        runishMainCodeUnsat("public function main(x: Int): Int { return if(x > 0i) then x else (5i // 0i); }", "(assert (not (is-@Result-err (Main@main 0))))");

        runishMainCodeUnsat("public function main(x: Int): Int { return if(x > 0i) then (5i // 0i) else x; }", "(assert (not (= (@Result-ok 0) (Main@main 0))))");
        runishMainCodeUnsat("public function main(x: Int): Int { return if(x > 0i) then (5i // 0i) else (5i // 0i); }", "(assert (not (is-@Result-err (Main@main 0))))");

        runishMainCodeUnsat("public function main(): Int { return if(1i == 2i // 2i) then 2i else 3i; }", "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat("public function main(): Int { return if(1i == 2i // 2i) then 2i else 3i // 0i; }", "(assert (not (= (@Result-ok 2) Main@main)))");
    });

    it("should SMT exec simple refine", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); return if(x)!none then 2i else 3i; }", "(assert (not (= 2 Main@main)))");

        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); return if(x)none then 2i // 0i else 3i; }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); return if(x)!none then 2i else 3i // 0i; }", "(assert (not (= (@Result-ok 2) Main@main)))");
    });

    it("should SMT exec simple bind", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); return if(x)@!none then $x else 3i; }", "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); return if(x)@none then 2i // 0i else $x; }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); return if(x)@!none then $x else 3i // 0i; }", "(assert (not (= (@Result-ok 3) Main@main)))");
    });

    /*
    it("should exec expressions w/ itest", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); return if(x)!none then 2i else 3i; }", "2i");
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); return if(x)some then 2i else 3i; }", "2i");
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); return if(x)<Some<Int>> then 2i else 3i; }", "2i");

        runMainCode("public function main(): Int { let x: Option<Int> = some(1i); return if(x)@!none then $x else 3i; }", "1i");
        runMainCode("public function main(): Int { let x: Int = 1i; return if(x < 3i) then 0i else x; }", "0i");
        
        runMainCode("public function main(): Int { let x: Int = 1i; return if(if(x < 3i) then none else some(x))@!none then $_ else 3i; }", "3i");
        runMainCode("public function main(): Int { let x: Int = 5i; return if(if(x < 3i) then none else some(x))@!none then $_ else 3i; }", "5i");
        
        runMainCode("public function main(): Int { let x: Option<Int> = some(1i); return if($y = x)@<Some<Int>> then $y.value else 3i; }", "1i");
        runMainCode("public function main(): Int { let x: Option<Int> = some(1i); return if($y = x)@some then $y else 3i; }", "1i");
        runMainCode("public function main(): Int { let x: Option<Int> = none; return if($y = x)@some then $y else 3i; }", "3i");
    });
    */
});

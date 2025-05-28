"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- IfElse Statement", () => {
    it("should SMT exec simple ifs", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { if(x == 0i) { return 3i; } else { return 1i; } }", "(assert (not (= 3 (Main@main 0))))");
        runishMainCodeUnsat("public function main(x: Int): Int { if(x == 0i) { return 3i; } else { return 1i; } }", "(assert (not (= 1 (Main@main 1))))");

        runishMainCodeUnsat("public function main(x: Int): Int { if(x == 0i) { return 3i; } else { ; } return 1i; }", "(assert (not (= 1 (Main@main 3))))");
    
        runishMainCodeUnsat("public function main(x: Int): Int { if(x == 0i) { return 3i; } else { return 1i // 0i; } }", "(assert (not (= (@Result-ok 3) (Main@main 0))))");
        runishMainCodeUnsat("public function main(x: Int): Int { if(x == 0i) { return 3i // 0i; } else { return 1i; } }", "(assert (not (= @Result-err-other (Main@main 0))))");
    });

    it("should smt check simple simple", function () {
        checkProperties("public function main(): Int { if(true) { return 2i; } else { return 3i; } }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Int 2 )" }]);
        checkProperties("public function main(): Int { if(false) { return 2i; } else {;} return 3i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Int 3 )" }]);
    });


/*
    it("should SMT exec itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } else { return 1i; } }", "3i");
        runMainCode("public function main(): Int { let x: Option<Int> = none; if(x)some { return 3i; } else { return 1i; } }", "1i");
    });

    it("should SMT exec binder itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $x; } else { return 1i; } }", "3i");
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if($y = x)@some { return $y; } else { return 1i; } }", "3i");

        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@none { return 1i; } else { return $x; } }", "3i");
        runMainCode("public function main(): Int { let x: Option<Int> = none; if(x)@none { return 1i; } else { return $x; } }", "1i");
    });

    it("should SMT exec binder & reflow itest ifs", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); if(x)@@!some { return 0i; } else { ; } return x; }", "3i");
    });
*/
});

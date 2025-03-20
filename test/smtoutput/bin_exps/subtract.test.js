"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Simple subtraction", () => {
    it("should smt eval simple", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { return x - 2i; }", "(declare-const b Int) (assert (= b (Main@main 3))) (assert (not (= b 1)))");

        runishMainCodeUnsat("public function main(x: Nat): Nat { return x - 2n; }", "(declare-const b (@Result Nat)) (assert (= b (Main@main 3))) (assert (not (= b (@Result-ok 1))))");
        runishMainCodeUnsat("public function main(x: Nat): Nat { return x - 2n; }", "(declare-const b (@Result Nat)) (assert (= b (Main@main 1))) (assert (not (= b @Result-err-other)))");
    });
});

describe ("SMT check props -- Simple subtraction", () => {
    it("should smt eval simple", function () {
        checkProperties("public function main(x: Nat): Nat { return x - 2n; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main ((x Nat)) (@Result Nat) (ite (< x 2) (as @Result-err-other (@Result Nat)) (@Result-ok (- x 2))) )" }]);
    });
});



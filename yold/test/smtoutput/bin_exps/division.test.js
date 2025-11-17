"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Simple div", () => {
    it("should smt eval simple", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { return 10i // x; }", "(declare-const b (@Result Int)) (assert (= b (Main@main 5))) (assert (is-@Result-err b))");
        runishMainCodeUnsat("public function main(x: Int): Int { return 10i // x; }", "(declare-const b (@Result Int)) (assert (= b (Main@main 0))) (assert (not (is-@Result-err b)))");

        runishMainCodeUnsat("public function main(x: Int): Int { return x // 2i; }", "(declare-const b (@Result Int)) (assert (= b (Main@main 8))) (assert (not (= b (@Result-ok 4))))");
    });
});

describe ("SMT check props -- Simple div", () => {
    it("should smt eval simple", function () {
        checkProperties("public function main(x: Nat): Nat { return 10n // x; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main ((x Nat)) (@Result Nat) (ite (= x Nat@zero) ((as @Result-err (@Result Nat)) @err-other) (@Result-ok (/ 10 x))) )" }]);
    });
});


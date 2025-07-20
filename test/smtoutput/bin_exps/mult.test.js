"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Simple mult", () => {
    it("should smt eval simple", function () {
        runishMainCodeUnsat("public function main(x: Nat): Nat { return x * 0n; }", "(declare-const b Int) (assert (= b (Main@main 3))) (assert (not (= b 0)))");
        //runishMainCodeUnsat("public function main(x: Float): Float { return x * 2.0f; }", "(declare-const b Real) (assert (= b (Main@main 3))) (assert (not (= b 6.0)))");
    });
});

describe ("SMT check props -- Simple mult", () => {
    it("should smt eval simple", function () {
        checkProperties("public function main(x: Nat): Nat { return x * 2n; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main ((x Nat)) Nat (* x 2) )" }]);
    });
});



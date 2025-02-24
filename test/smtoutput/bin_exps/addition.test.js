"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Simple addition", () => {
    it("should smt eval simple", function () {
        runishMainCodeUnsat("public function main(x: Nat): Nat { return x + 2n; }", "(declare-const a Nat) (assert (= a 3)) (declare-const b Nat) (assert (= b (Main@main a))) (assert (not (= b 5)))");
    });
});

describe ("SMT check props -- Simple addition", () => {
    it("should smt eval simple", function () {
        checkProperties("public function main(x: Nat): Nat { return x + 2n; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main ((x Nat)) Nat (+ x 2) )" }]);
    });
});



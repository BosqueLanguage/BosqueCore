"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Simple div", () => {
    it("should smt eval simple", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { return 10i // x; }", "(declare-const b (@Result Int)) (assert (= b (Main@main 5))) (assert (not (= b (@Result-ok 2))))");
        runishMainCodeUnsat("public function main(x: Int): Int { return 10i // x; }", "(declare-const b (@Result Int)) (assert (= b (Main@main 0))) (assert (not (= b @Result-err-other)))");
    });
});

describe ("SMT check props -- Simple div", () => {
    it("should smt eval simple", function () {
        checkProperties("public function main(x: Nat): Nat { return 10 // x; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "unk1" }]);
    });
});


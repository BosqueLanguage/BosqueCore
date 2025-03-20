"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Simple mult", () => {
    it("should smt eval simple", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { return x * 2i; }", "(declare-const b Int) (assert (= b (Main@main 3))) (assert (not (= b 1)))");
    });
});

describe ("SMT check props -- Simple mult", () => {
    it("should smt eval simple", function () {
        checkProperties("public function main(x: Nat): Nat { return x * 2n; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "unk2" }]);
    });
});



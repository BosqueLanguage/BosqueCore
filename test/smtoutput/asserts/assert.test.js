"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- simple abort", () => {
    it("should SMT eval simple abort", function () {
        runishMainCodeUnsat("public function main(): Int { abort; }", "(assert (not (= Main@main @Result-err-other)))");
    });
});

describe ("SMT -- simple assert", () => {
    it("should SMT eval simple assert (ok)", function () {
        runishMainCodeUnsat("public function main(): Int { assert true; return 1i; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= 1 a)))");
    });

    it("should SMT eval error assert (fail)", function () {
        runishMainCodeUnsat("public function main(): Int { assert false; return 1i; }", "(declare-const a (@Result Int)) (assert (= a Main@main)) (assert (not (= @Result-err-other a)))");
    });
});

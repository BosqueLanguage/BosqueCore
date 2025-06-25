"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- simple abort", () => {
    it("should SMT eval simple abort", function () {
        runishMainCodeUnsat("public function main(): Int { abort; }", "(assert (not (is-@Result-err Main@main)))");
    });
});

describe ("SMT -- simple assert", () => {
    it("should SMT eval simple assert (ok)", function () {
        runishMainCodeUnsat("public function main(): Int { assert true; return 1i; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= 1 a)))");
    });

    it("should SMT eval with assert (ok)", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { assert x != 1i; return x; }", "(declare-const a (@Result Int)) (assert (= a (Main@main 2))) (assert (not (= (@Result-ok 2) a)))");
    });

    it("should SMT eval simple assert (fail)", function () {
        runishMainCodeUnsat("public function main(): Int { assert false; return 1i; }", "(declare-const a (@Result Int)) (assert (= a Main@main)) (assert (not (is-@Result-err a)))");
    });

    it("should SMT eval with assert (fail)", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { assert x != 1i; return x; }", "(declare-const a (@Result Int)) (assert (= a (Main@main 1))) (assert (not (is-@Result-err a)))");
    });
});

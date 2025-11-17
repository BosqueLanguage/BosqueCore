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

/*
describe ("SMT -- simple validate", () => {
    it("should exec simple validate", function () {
        runMainCode("public function main(): Int { validate true; return 1i; }", "1i");
    });

    it("should exec error validate", function () {
        runMainCodeError("public function main(): Int { validate 1i > (1i + 2i) || false; return 1i; }", "Error -- (1i > (1i + 2i)) || false @ test.bsq:3");
        runMainCodeError("public function main(): Int { validate['ec-0'] false; return 1i; }", "Error -- false['ec-0'] @ test.bsq:3");
    });
});
*/

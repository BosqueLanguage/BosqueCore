"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- simple declare-assign only", () => {
    it("should SMT eval simple declare-assign", function () {
        runishMainCodeUnsat("public function main(): Int { var x: Int = 5i; return x; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= 5 a)))");
        runishMainCodeUnsat("public function main(): Bool { let x: Bool = true; return x; }", "(assert (not Main@main))");
    });

    it("should SMT eval simple declare-assign infer type", function () {
        runishMainCodeUnsat("public function main(): Int { var x = 5i; return x; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= 5 a)))");
        runishMainCodeUnsat("public function main(): Bool { let x = true; return x; }", "(assert (not Main@main))");
    });
});

describe ("SMT evaluate -- simple assign", () => {
    it("should SMT eval simple assign", function () {
        runishMainCodeUnsat("public function main(): Int { var x: Int = 5i; x = 2i; return x; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= 2 a)))");
        runishMainCodeUnsat("public function main(): Int { var x: Int = 5i; x = 2i; x = 0i; return x; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= 0 a)))");
    });
});


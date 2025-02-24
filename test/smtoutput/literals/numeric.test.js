"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Nat", () => {
    it("should smt eval simple nats", function () {
        runishMainCodeUnsat("public function main(): Nat { return 0n; }", "(declare-const a Nat) (assert (= a Main@main)) (assert (not (= a 0)))");
        runishMainCodeUnsat("public function main(): Nat { return +2n; }", "(declare-const a Nat) (assert (= a Main@main)) (assert (not (= a 2)))");
    });
});

describe ("SMT evaluate -- Int", () => {
    it("should smt eval simple ints", function () {
        runishMainCodeUnsat("public function main(): Int { return 0i; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= a 0)))");
        runishMainCodeUnsat("public function main(): Int { return -2i; }", "(declare-const a Int) (assert (= a Main@main)) (assert (not (= a -2)))");
    });
});

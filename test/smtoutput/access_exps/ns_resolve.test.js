"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Resolvable NS consts", () => {
    it("should smt eval simple resolvable ns consts", function () {
        runishMainCodeUnsat("const c1: Nat = 0n; public function main(): Nat { return Main::c1; }", "(declare-const a Bool) (assert (= a Main@main)) (assert (not (= 0 a)))");
        checkProperties("const c1: Nat = 0n; public function main(): Nat { return Main::c1; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "ff1" }]);
    });

    it("should smt eval multi resolvable ns consts", function () {
        runishMainCodeUnsat("const c2: Nat = 0n; const c1: Nat = Main::c2; public function main(): Nat { return Main::c1; }", "(declare-const a Bool) (assert (= a Main@main)) (assert (not (= 0 a)))");
        checkProperties("const c2: Nat = 0n; const c1: Nat = Main::c2; public function main(): Nat { return Main::c1; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "ff2" }]);
    });
});

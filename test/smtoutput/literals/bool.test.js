"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Bool", () => {
    it("should smt eval simple bools", function () {
        runishMainCodeUnsat("public function main(): Bool { return true; }", "(declare-const a Bool) (assert (= a Main@main)) (assert (not a))");
        runishMainCodeUnsat("public function main(): Bool { return false; }", "(declare-const a Bool) (assert (= a Main@main)) (assert a)");
    });
});

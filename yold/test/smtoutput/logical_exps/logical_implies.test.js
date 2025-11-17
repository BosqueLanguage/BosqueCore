"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- logical implies", () => {
    it("should smt exec simple implies", function () {
        runishMainCodeUnsat("public function main(a: Int): Bool { return a == 0i ==> false; }", "(assert (Main@main 0))");
        runishMainCodeUnsat("public function main(a: Int): Bool { return a == 0i ==> true; }", "(assert (not (Main@main 1)))");

        runishMainCodeUnsat("public function main(a: Int): Bool { return (a // 1i == a) ==> true; }", "(assert (not (= (@Result-ok true) (Main@main 1))))");
    });

    it("should smt exec sc implies", function () {
        checkProperties("public function main(): Bool { return false ==> (1i // 0i) == 1i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Bool true )" }]);
    });
});

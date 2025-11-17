"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- logical and", () => {
    it("should smt exec simple and", function () {
        runishMainCodeUnsat("public function main(a: Int): Bool { return a == 0i && true; }", "(assert (Main@main 1))");
        runishMainCodeUnsat("public function main(a: Int): Bool { return a != 1i && true; }", "(assert (not (Main@main 0)))");

        runishMainCodeUnsat("public function main(a: Int): Bool { return a == 0i && (a // 2i == 1i); }", "(assert (not (= (@Result-ok false) (Main@main 1))))");
    });

    it("should smt exec sc and", function () {
        checkProperties("public function main(): Bool { return false && (1i // 0i) == 1i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Bool false )" }]);
    });
});

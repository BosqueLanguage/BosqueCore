"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- op and", () => {
    it("should smt exec simple and", function () {
        runishMainCodeUnsat("public function main(): Bool { return /\\(true); }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { return /\\(true, false); }", "(assert Main@main)");

        runishMainCodeUnsat("public function main(a: Int): Bool { return /\\(a != 0i, a != 1i, a != 2i); }", "(assert (Main@main 1))");
        runishMainCodeUnsat("public function main(a: Int): Bool { return /\\(a != 0i, a != 1i, a != 2i); }", "(assert (not (Main@main 5)))");
    });

    it("should smt check simple simple", function () {
        checkProperties("public function main(): Bool { return /\\(true, false); }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Bool false )" }]);
        checkProperties("public function main(): Bool { return /\\(true, 1i == 0i); }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Bool (= 1 0) )" }]);
    });
});

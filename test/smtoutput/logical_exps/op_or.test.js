"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- op or", () => {
    it("should smt exec simple or", function () {
        runishMainCodeUnsat("public function main(): Bool { return \\/(true); }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { return \\/(true, false); }", "(assert (not Main@main))");
        
        runishMainCodeUnsat("public function main(a: Int): Bool { return \\/(a == 0i, a == 1i, a == 2i); }", "(assert (Main@main 5))");
        runishMainCodeUnsat("public function main(a: Int): Bool { return \\/(a == 0i, a == 1i, a == 2i); }", "(assert (not (Main@main 2)))");
    });

    it("should smt check simple simple", function () {
        checkProperties("public function main(): Bool { return \\/(true, false); }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Bool true )" }]);
        checkProperties("public function main(x: Bool): Bool { return \\/(false, 1i == 0i, x); }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main ((x Bool)) Bool (or (= 1 0) x) )" }]);
    });
});

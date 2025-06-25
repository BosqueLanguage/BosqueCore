"use strict";

import { runishMainCodeUnsat, checkProperties } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- logical or", () => {
    it("should exec simple or", function () {
        runishMainCodeUnsat("public function main(a: Int ): Bool { return a == 1i || false; }", "(assert (not (Main@main 1)))");
        runishMainCodeUnsat("public function main(a: Int): Bool { return a == 1i || false; }", "(assert (Main@main 2))");
    });

    it("should exec sc or", function () {
        checkProperties("public function main(): Bool { return true || (1i // 0i) == 1i; }", [{ pkey: ";;--FUNCTION_DECLS--;;", expected: "(define-fun Main@main () Bool true )" }]);
    });
});

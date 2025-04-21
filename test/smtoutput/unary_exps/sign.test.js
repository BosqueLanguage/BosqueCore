"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- Simple numeric sign", () => {
    it("should SMT exec simple not", function () {
        runishMainCodeUnsat("public function main(x: Int): Int { return -x; }", "(assert (not (= 3 (Main@main -3))))");
        runishMainCodeUnsat("public function main(x: Nat): Nat { return +x; }", "(assert (not (= 5 (Main@main 5))))");
    });
});

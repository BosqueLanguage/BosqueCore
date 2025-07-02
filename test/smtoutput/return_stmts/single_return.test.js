"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- simple return", () => {
    it("should smt exec simple returns", function () {
        runishMainCodeUnsat('public function main(): Int { return 2i; }', "(assert (not (= 2 Main@main)))");
    });
});

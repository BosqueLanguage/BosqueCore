"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- basic <", () => {
    it("should SMT exec compare simple types", function () {
        runishMainCodeUnsat("public function main(): Bool { return 0n < 1n; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { return +2i < -2i; }", "(assert Main@main)");

        runishMainCodeUnsat("public function main(): Bool { return 1n < 1n; }", "(assert Main@main)");
    });
});

describe ("SMT -- basic <=", () => {
    it("should SMT exec compare simple types", function () {
        runishMainCodeUnsat("public function main(): Bool { return 0n <= 1n; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { return +2i <= -2i; }", "(assert Main@main)");

        runishMainCodeUnsat("public function main(): Bool { return 1n <= 1n; }", "(assert (not Main@main))");
    });
});

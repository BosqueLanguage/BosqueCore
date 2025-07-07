"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT List -- allof basic", () => {
    it("should smt do simple allof", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.allOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 2i}.allOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-2i}.allOf(pred(x) => x >= 0i); }', "(assert Main@main)");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, -1i}.allOf(pred(x) => x >= 0i); }', "(assert Main@main)");
    });
});

describe ("SMT List -- noneof basic", () => {
    it("should smt do simple noneof", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.noneOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, -2i}.noneOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{2i}.noneOf(pred(x) => x >= 0i); }', "(assert Main@main)");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, -1i}.noneOf(pred(x) => x >= 0i); }', "(assert Main@main)");
    });
});

describe ("SMT List -- someof basic", () => {
    it("should smt do simple someof", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.someOf(pred(x) => x >= 0i); }', "(assert Main@main)");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, 2i}.someOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-2i}.someOf(pred(x) => x >= 0i); }', "(assert Main@main)");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, -1i}.someOf(pred(x) => x >= 0i); }', "(assert Main@main)");
    });
});

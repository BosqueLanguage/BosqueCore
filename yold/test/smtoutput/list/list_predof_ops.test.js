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

    it("should smt do simple allof w/err", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 2i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-2i, 1i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 0i, 3i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, 0i, 3i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");
    });
});

describe ("SMT List -- noneof basic", () => {
    it("should smt do simple noneof", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.noneOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, -2i}.noneOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{2i}.noneOf(pred(x) => x >= 0i); }', "(assert Main@main)");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, -1i}.noneOf(pred(x) => x >= 0i); }', "(assert Main@main)");
    });

    it("should smt do simple noneof w/err", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, -2i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, -1i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, 0i, 3i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 0i, 3i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");
    });
});

describe ("SMT List -- someof basic", () => {
    it("should smt do simple someof", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.someOf(pred(x) => x >= 0i); }', "(assert Main@main)");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, 2i}.someOf(pred(x) => x >= 0i); }', "(assert (not Main@main))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-2i}.someOf(pred(x) => x >= 0i); }', "(assert Main@main)");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, -1i}.someOf(pred(x) => x >= 0i); }', "(assert Main@main)");
    });

    it("should smt do simple someof w/err", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, 2i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, -1i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{-1i, 0i, 3i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 0i, 3i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
    });
});

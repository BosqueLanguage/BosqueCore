"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- basic strict equals", () => {
    it("should SMT exec strict equals operations", function () {
        runishMainCodeUnsat("public function main(): Bool { return 0n === 1n; }", "(assert Main@main)");
        runishMainCodeUnsat("public function main(): Bool { return 0n !== 1n; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { return 'ok' !== 'yes'; }", "(assert (not Main@main))");

        runishMainCodeUnsat("public function main(): Bool { let x = 3i; let y = 4i; return x !== y; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { let x = 3i; let y = 4i; return x === y; }", "(assert Main@main)");
    });
});

describe ("SMT -- Option strict equals", () => {
    it("should smt exec strict equals option operations", function () {
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = some(3i); return x === none; }", "(assert Main@main)");
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = some(3i); return x !== none; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = some(3i); return none === x; }", "(assert Main@main)");

        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = none; return x === none; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = none; return x !== none; }", "(assert Main@main)");
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = none; return none === x; }", "(assert (not Main@main))");

        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = none; return x === 3i; }", "(assert Main@main)");
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = none; return 3i === x; }", "(assert Main@main)");

        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = some(3i); return x === 3i; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = some(4i); return 3i === x; }", "(assert Main@main)");
    });

    it("should smt exec strict equals option operations (w/err)", function () {
        runishMainCodeUnsat("public function main(): Bool { let x: Option<Int> = some(3i); return x === 4i // 0i; }", "(assert (not (is-@Result-err Main@main)))");
    });
});
/*
describe ("SMT -- type alias strict equals", () => {
    it("should smt exec type alias strict equals operations", function () {
        runishMainCodeUnsat("type Foo = Int; public function main(): Bool { return 1i<Foo> === 1i<Foo>; }", "true");
        runishMainCodeUnsat("type Foo = Int; public function main(): Bool { return 1i<Foo> !== 1i<Foo>; }", "false");

        runishMainCodeUnsat("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x === none; }", "false");
        runishMainCodeUnsat("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 0i<Foo>; }", "true");
        runishMainCodeUnsat("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 3i<Foo>; }", "false");
    });
});
*/

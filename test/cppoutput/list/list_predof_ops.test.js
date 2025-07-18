"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";


describe ("CPP Emit Evaluate List -- allof basic", () => {
    it("should do simple allof", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.allOf(pred(x) => x >= 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i}.allOf(pred(x) => x >= 0i); }', "true");

        runMainCode('public function main(): Bool { return List<Int>{-2i}.allOf(pred(x) => x >= 0i); }', "false");
        runMainCode('public function main(): Bool { return List<Int>{1i, -1i}.allOf(pred(x) => x >= 0i); }', "false");
    });

/*
    it("should smt do simple allof w/err", function () {
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runMainCode('public function main(): Bool { return List<Int>{-2i, 1i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");

        runMainCode('public function main(): Bool { return List<Int>{1i, 0i, 3i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Bool { return List<Int>{-1i, 0i, 3i}.allOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");
    });
*/
});

describe ("CPP Emit Evaluate List -- noneof basic", () => {
    it("should do simple noneof", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.noneOf(pred(x) => x >= 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{-1i, -2i}.noneOf(pred(x) => x >= 0i); }', "true");

        runMainCode('public function main(): Bool { return List<Int>{2i}.noneOf(pred(x) => x >= 0i); }', "false");
        runMainCode('public function main(): Bool { return List<Int>{1i, -1i}.noneOf(pred(x) => x >= 0i); }', "false");
    });

/*
    it("should smt do simple noneof w/err", function () {
        runMainCode('public function main(): Bool { return List<Int>{-1i, -2i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runMainCode('public function main(): Bool { return List<Int>{1i, -1i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");

        runMainCode('public function main(): Bool { return List<Int>{-1i, 0i, 3i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Bool { return List<Int>{1i, 0i, 3i}.noneOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");
    });
*/
});

describe ("CPP Emit Evaluate List -- someof basic", () => {
    it("should do simple someof", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.someOf(pred(x) => x >= 0i); }', "false");
        runMainCode('public function main(): Bool { return List<Int>{-1i, 2i}.someOf(pred(x) => x >= 0i); }', "true");

        runMainCode('public function main(): Bool { return List<Int>{-2i}.someOf(pred(x) => x >= 0i); }', "false");
        runMainCode('public function main(): Bool { return List<Int>{-1i, -1i}.someOf(pred(x) => x >= 0i); }', "false");
    });

/*
    it("should smt do simple someof w/err", function () {
        runMainCode('public function main(): Bool { return List<Int>{-1i, 2i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runMainCode('public function main(): Bool { return List<Int>{-1i, -1i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok false) Main@main)))");

        runMainCode('public function main(): Bool { return List<Int>{-1i, 0i, 3i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Bool { return List<Int>{1i, 0i, 3i}.someOf(pred(x) => { assert x != 0i; return x >= 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
    });
*/
});

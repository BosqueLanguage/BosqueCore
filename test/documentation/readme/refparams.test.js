"use strict";

import { runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

describe ("ref param collections", () => {
    it("should show ref param collection operation", function () {
        runTestSet('public function main(x: Nat): Nat { let m = Map<Int, Nat>{}; return m.add(0i, x).add(1i, x + 1n).size(); }', [['6n', '2n']], []);
        runTestSet('public function main(x: Nat): Nat { var m = Map<Int, Nat>{}; ref m.add(0i, x); ref m.add(1i, x + 1n); return m.size(); }', [['6n', '2n']], []);

        runTestSet('public function main(x: Nat): Nat { let m = Map<Int, Nat>{}; return m.add(0i, x).add(1i, x + 1n).get(1i); }', [['6n', '7n']], []);
        runTestSet('public function main(x: Nat): Nat { var m = Map<Int, Nat>{}; ref m.add(0i, x); ref m.add(1i, x + 1n); return m.get(1i); }', [['6n', '7n']], []);
    });
});

describe ("ref param objs", () => {
    it("should show ref param counter", function () {
        runTestSet('entity Ctr { field vv: Nat = 0n; method next(): Ctr { return Ctr{ vv = this.vv + 1n }; } } public function main(x: Nat): Nat { let ctr = Ctr{}; let ctr1 = ctr.next(); let ctr2 = ctr1.next(); return ctr2.vv; }', [['0n', '2n']], []);

        runTestSet('entity Ctr { field vv: Nat = 0n; ref method next() { ref this[vv = $vv + 1n]; } } public function main(x: Nat): Nat { ref ctr = Ctr{}; ref ctr.next(); ref ctr.next(); return ctr.vv; }', [['0n', '2n']], []);
    });
});

describe ("out and out? params", () => {
    it("should show out and out? param operation", function () {
        runTestSet('function tryParse(str: CString, out? vval: Int): Bool { vval = 1i; return true; } public function main(s: CString): Int { var vv: Int; if(tryParse(s, out? vv)) { return vv; } else { return 0i; } }', [['"ok"', '1i']], []);
    });
});

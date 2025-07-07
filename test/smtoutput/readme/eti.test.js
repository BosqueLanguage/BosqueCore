"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

const flowit = 'function flowit(x: Option<Nat>): Nat { if(x)@none { return 0n; } else { return $x + 10n; } }';
const restrict = 'function restrict(x: Option<Nat>): Nat { if(x)@@none { return 0n; } return x + 10n; }';

describe ("SMT flowit exec", () => {
    it("smt flowit should succeed", function () {
        runishMainCodeUnsat(`${flowit} public function main(): Nat { return flowit(none); }`, "(assert (not (= 0 Main@main)))");
        runishMainCodeUnsat(`${flowit} public function main(): Nat { return flowit(some(5n)); }`, "(assert (not (= 15 Main@main)))");
    });
});

describe ("SMT restrict exec", () => {
    it("smt restrict should succeed", function () {
        runishMainCodeUnsat(`${restrict} public function main(): Nat { return restrict(none); }`, "(assert (not (= 0 Main@main)))");
        runishMainCodeUnsat(`${restrict} public function main(): Nat { return restrict(some(5n)); }`, "(assert (not (= 15 Main@main)))");
    });
});

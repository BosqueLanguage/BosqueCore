"use strict";

import { runMainCode } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const flowit = 'function flowit(x: Option<Nat>): Nat { if(x)@none { return 0n; } else { return $x + 10n; } }';
const restrict = 'function restrict(x: Option<Nat>): Nat { if(x)@@none { return 0n; } return x + 10n; }';

describe ("flowit exec", () => {
    it("flowit should succeed", function () {
        runMainCode(`${flowit} public function main(): Nat { return flowit(none); }`, "0n");
        runMainCode(`${flowit} public function main(): Nat { return flowit(some(5n)); }`, "15n"); 
    });
});

describe ("restrict exec", () => {
    it("restrict should succeed", function () {
        runMainCode(`${restrict} public function main(): Nat { return restrict(none); }`, "0n");
        runMainCode(`${restrict} public function main(): Nat { return restrict(some(5n)); }`, "15n"); 
    });
});

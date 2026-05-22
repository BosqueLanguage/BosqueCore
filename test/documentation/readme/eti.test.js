"use strict";

import { runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const flowit = 'function flowit(x: Option<Nat>): Nat { if(x)@none { return 0n; } else { return $x + 10n; } }';

describe ("flowit exec", () => {
    it("flowit should succeed", function () {
        runTestSet(`${flowit} public function main(x: Option<Nat>): Nat { return flowit(x); }`, [['none', '0n'], ['some(5n)', '15n']], []);
    });
});


"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Nats Power", () => {
    it("should compute powers generally", function () {
        runTestSet('public function main(x: Nat): Nat { return Nat::pow(x, 5n); }', [['0n', '0n'], ['1n', '1n'], ['2n', '32n'], ['3n', '243n']], ['16777216n']);
        runTestSet('public function main(y: Nat): Nat { return Nat::pow(3n, y); }', [['0n', '1n'], ['1n', '3n'], ['2n', '9n'], ['3n', '27n']], ['904n']);
    });
});

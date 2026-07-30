"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Floats Power", () => {
    it("should compute powers generally", function () {
        runTestSet('public function main(x: Float): Float { return Float::pow(x, 5.0f); }', [['0.0f', '0.0f'], ['1.0f', '1.0f'], ['2.0f', '32.0f'], ['3.0f', '243.0f']], []);
        runTestSet('public function main(y: Float): Float { return Float::pow(3.0f, y); }', [['0.0f', '1.0f'], ['1.0f', '3.0f'], ['2.0f', '9.0f'], ['3.0f', '27.0f']], []);

        runTestSet('public function main(x: Float): Float { return Float::pow(x, -2.0f); }', [['1.0f', '1.0f'], ['2.0f', '0.25f'], ['3.0f', '0.111111111111f']], ['0.0f']);
    });
});

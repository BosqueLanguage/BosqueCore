"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("String -- construct empty and isEmpty", () => {
    it("should create simple string", function () {
        runTestSet('public function main(z: String): Bool { return z.empty(); }', [['""', 'true'], ['"non-empty"', 'false']], []);
    });
});

describe ("String -- immediate and size", () => {
    it("should create and size", function () {
        runTestSet('public function main(z: String): Nat { return z.size(); }', [['""', '0n'], ['"a"', '1n'], ['"abc"', '3n'], ['"🌵🌵"', '2n']], []);
    });
});

describe ("String -- big parse", () => {
    it("should test big parsing", function () {
        runTestSet('public function main(z: String): String { return z; }', [['"abcdefghijklmonpqrstuvwxyz!!!1234567890bigbrowndog"', '"abcdefghijklmonpqrstuvwxyz!!!1234567890bigbrowndog"']], []);
    });
});

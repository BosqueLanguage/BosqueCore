"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- construct empty and isEmpty", () => {
    it("should create simple cstring", function () {
        runTestSet('public function main(z: CString): Bool { return z.empty(); }', [['""', 'true'], ['"non-empty"', 'false']], []);
    });
});

describe ("CString -- immediate and size", () => {
    it("should create and size", function () {
        runTestSet('public function main(z: CString): Nat { return z.size(); }', [['""', '0n'], ['"a"', '1n'], ['"abc"', '3n']], []);
    });
});

describe ("CString -- big parse", () => {
    it("should test big parsing", function () {
        runTestSet('public function main(z: CString): CString { return z; }', [['"abcdefghijklmonpqrstuvwxyz!!!1234567890bigbrowndog"', "'abcdefghijklmonpqrstuvwxyz!!!1234567890bigbrowndog'"]], []);
    });
});

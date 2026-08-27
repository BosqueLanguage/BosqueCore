"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Nat Operations", () => {
    it("should compute tostring", function () {
        runTestSet('public function main(n: Nat): CString { return Nat::toCString(n); }', [['0n', "'0n'"], ['3n', "'3n'"]], []);

        runTestSet('public function main(n: Nat): String { return Nat::toString(n); }', [['0n', '"0n"'], ['3n', '"3n"']], []);
    });
    
    it("should compute powers generally", function () {
        runTestSet('public function main(x: Nat): Nat { return Nat::pow(x, 5n); }', [['0n', '0n'], ['1n', '1n'], ['2n', '32n'], ['3n', '243n']], ['16777216n']);
        runTestSet('public function main(y: Nat): Nat { return Nat::pow(3n, y); }', [['0n', '1n'], ['1n', '3n'], ['2n', '9n'], ['3n', '27n']], ['904n']);
    });
});

describe ("Int Operations", () => {
    it("should compute tostring", function () {
        runTestSet('public function main(i: Int): CString { return Int::toCString(i); }', [['0i', "'0i'"], ['3i', "'3i'"], ['-3i', "'-3i'"]], []);

        runTestSet('public function main(i: Int): String { return Int::toString(i); }', [['0i', '"0i"'], ['3i', '"3i"'], ['-3i', '"-3i"']], []);
    });
});

describe ("ChkNat Operations", () => {
    it("should compute tostring", function () {
        runTestSet('public function main(n: ChkNat): CString { return ChkNat::toCString(n); }', [['0N', "'0N'"], ['3N', "'3N'"], ['ChkNat::npos', "'ChkNat::npos'"]], []);

        runTestSet('public function main(n: ChkNat): String { return ChkNat::toString(n); }', [['0N', '"0N"'], ['3N', '"3N"'], ['ChkNat::npos', '"ChkNat::npos"']], []);
    });
});

describe ("ChkInt Operations", () => {
    it("should compute tostring", function () {
        runTestSet('public function main(i: ChkInt): CString { return ChkInt::toCString(i); }', [['0I', "'0I'"], ['3I', "'3I'"], ['-3I', "'-3I'"], ['ChkInt::npos', "'ChkInt::npos'"]], []);

        runTestSet('public function main(i: ChkInt): String { return ChkInt::toString(i); }', [['0I', '"0I"'], ['3I', '"3I"'], ['-3I', '"-3I"'], ['ChkInt::npos', '"ChkInt::npos"']], []);
    });
});


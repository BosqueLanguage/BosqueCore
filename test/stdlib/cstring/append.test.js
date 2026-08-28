"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- append", () => {
    it("should append", function () {
        runTestSet("public function main(z: CString): CString { return ''.append(z); }", [['""', "''"], ['"a"', "'a'"]], []);
        runTestSet("public function main(z: CString): CString { return z.append(''); }", [['""', "''"], ['"a"', "'a'"]], []);

        runTestSet("public function main(z: CString): CString { return 'abc'.append(z); }", [['"xyz"', "'abcxyz'"], ['"d"', "'abcd'"], ['"123456789012345"', "'abc123456789012345'"]], []);
        runTestSet("public function main(z: CString): CString { return 'abc'.prepend(z); }", [['"xyz"', "'xyzabc'"], ['"d"', "'dabc'"], ['"123456789012345"', "'123456789012345abc'"]], []);

        runTestSet("public function main(z: CString): CString { return 'abc'.append(z).prepend('xyz'); }", [['"pqr"', "'xyzabcpqr'"], ['"d"', "'xyzabcd'"], ['"123456789012345"', "'xyzabc123456789012345'"]], []);
        runTestSet("public function main(z: CString): CString { return 'abc'.prepend(z).append('xyz'); }", [['"pqr"', "'pqrabcxyz'"], ['"d"', "'dabcxyz'"], ['"123456789012345"', "'123456789012345abcxyz'"]], []);
    });

    it("should concat", function () {
        runTestSet('public function main(z: List<CString>): CString { return CString::concatAll(z); }', [['List<CString>{"abc", "def"}', "'abcdef'"], ['List<CString>{"123"}', "'123'"], ['List<CString>{}', "''"]], []);

        runTestSet('public function main(z: List<CString>): CString { return CString::concat(); }', [['"abc"', "''"]], []);
        runTestSet('public function main(z: List<CString>): CString { return CString::concat(z); }', [['"abc"', "'abc'"], ['""', "''"]], []);
        runTestSet('public function main(z: List<CString>): CString { return CString::concat(z, z); }', [['"abc"', "'abcabc'"], ['"x"', "'xx'"], ['""', "''"]], []);
        runTestSet('public function main(z: List<CString>): CString { return CString::concat("abc", z, "xyz"); }', [['""', "'abcxyz'"], ['"123"', "'abc123xyz'"]], []);
    });

    it("should join", function () {
        runTestSet("public function main(z: List<CString>): CString { return CString::joinAll('.', z); }", [['List<CString>{"abc", "def"}', "'abc.def'"], ['List<CString>{"123"}', "'123'"], ['List<CString>{}', "''"]], []);

        runTestSet("public function main(z: List<CString>): CString { return CString::join('.'); }", [['"abc"', "''"]], []);
        runTestSet("public function main(z: List<CString>): CString { return CString::join('.', z); }", [['"abc"', "'abc'"], ['""', "''"]], []);
        runTestSet("public function main(z: List<CString>): CString { return CString::join('.', z, z); }", [['"abc"', "'abc.abc'"], ['"x"', "'x.x'"], ['""', "'.'"]], []);
        runTestSet("public function main(z: List<CString>): CString { return CString::join('.', 'abc', z, 'xyz'); }", [['""', "'abc..xyz'"], ['"123"', "'abc.123.xyz'"]], []);
    });
});


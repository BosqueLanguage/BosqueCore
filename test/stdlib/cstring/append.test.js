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
});


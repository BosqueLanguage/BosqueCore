"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe("CString split tests", () => {
    it("should split by char", () => {
        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CChar>(c'#'); }", [['""', "List<CString>{ '' }"], ['"abc"', "List<CString>{ 'abc' }"], ['"abc#"', "List<CString>{ 'abc', '' }"], ['"#"', "List<CString>{ '', '' }"], ['"#def"', "List<CString>{ '', 'def' }"], ['"123#def"', "List<CString>{ '123', 'def' }"], ['"#abc#"', "List<CString>{ '', 'abc', '' }"], ['"#abc#123"', "List<CString>{ '', 'abc', '123' }"], ['"##123"', "List<CString>{ '', '', '123' }"], ['"123#abc"', "List<CString>{ '123', 'abc' }"]], []);
    });

    it("should split by cstring", () => {
        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CString>(''); }", [['""', "List<CString>{ '' }"], ['"abc"', "List<CString>{ 'a', 'b', 'c' }"]], []);

        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CString>('###'); }", [['""', "List<CString>{ '' }"], ['"abc"', "List<CString>{ 'abc' }"], ['"abc###"', "List<CString>{ 'abc', '' }"], ['"###"', "List<CString>{ '', '' }"], ['"###def"', "List<CString>{ '', 'def' }"], ['"123###def"', "List<CString>{ '123', 'def' }"], ['"###abc###"', "List<CString>{ '', 'abc', '' }"], ['"###abc###123"', "List<CString>{ '', 'abc', '123' }"], ['"######123"', "List<CString>{ '', '', '123' }"], ['"123###abc"', "List<CString>{ '123', 'abc' }"]], []);
    });

    it("should split by cregex", () => {
        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CRegex>(/[0-9]*/c); }", [['""', "List<CString>{ '' }"], ['"abc"', "List<CString>{ 'a', 'b', 'c' }"]], []);

        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CRegex>(/'###'/c); }", [['""', "List<CString>{ '' }"], ['"abc"', "List<CString>{ 'abc' }"], ['"abc###"', "List<CString>{ 'abc', '' }"], ['"###"', "List<CString>{ '', '' }"], ['"###def"', "List<CString>{ '', 'def' }"], ['"123###def"', "List<CString>{ '123', 'def' }"], ['"###abc###"', "List<CString>{ '', 'abc', '' }"], ['"###abc###123"', "List<CString>{ '', 'abc', '123' }"], ['"######123"', "List<CString>{ '', '', '123' }"], ['"123###abc"', "List<CString>{ '123', 'abc' }"]], []);
    });
});

describe("CString split tests with WS management", () => {
    it("should split and discard empty", () => {
        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CString>('###', dropempty = true); }", [['""', "List<CString>{ }"], ['" abc "', "List<CString>{ ' abc ' }"], ['"abc###"', "List<CString>{ 'abc' }"], ['"###"', "List<CString>{ }"], ['" ###def"', "List<CString>{ ' ', 'def' }"], ['"123###def"', "List<CString>{ '123', 'def' }"], ['"###abc###"', "List<CString>{ 'abc' }"], ['"###abc###123"', "List<CString>{ 'abc', '123' }"], ['"######123"', "List<CString>{ '123' }"], ['"123###abc"', "List<CString>{ '123', 'abc' }"], ['"  ### "', "List<CString>{ '  ', ' ' }"]], []);
    });

    it("should split and trim", () => {
        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CString>('###', trim = true); }", [['""', "List<CString>{ '' }"], ['" abc "', "List<CString>{ 'abc' }"], ['"abc ### ### def "', "List<CString>{ 'abc', '', 'def' }"]], []);
    });

    it("should split, trim, and discard empty", () => {
        runTestSet("public function main(sstr: CString): List<CString> { return sstr.split<CString>('###', trim = true, dropempty = true); }", [['""', "List<CString>{ }"], ['" abc "', "List<CString>{ 'abc' }"], ['"abc ### ### def "', "List<CString>{ 'abc', 'def' }"], ['"### abc ###"', "List<CString>{ 'abc' }"]], []);
    });
});

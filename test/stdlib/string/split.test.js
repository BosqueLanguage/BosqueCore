"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe("String split tests", () => {
    it("should split by char", () => {
        runTestSet('public function main(sstr: String): List<String> { return sstr.split<UnicodeChar>(c"#"); }', [['""', 'List<String>{ "" }'], ['"abc"', 'List<String>{ "abc" }'], ['"abc#"', 'List<String>{ "abc", "" }'], ['"#"', 'List<String>{ "", "" }'], ['"#def"', 'List<String>{ "", "def" }'], ['"123#def"', 'List<String>{ "123", "def" }'], ['"#abc#"', 'List<String>{ "", "abc", "" }'], ['"#abc#123"', 'List<String>{ "", "abc", "123" }'], ['"##123"', 'List<String>{ "", "", "123" }'], ['"123#abc"', 'List<String>{ "123", "abc" }']], []);
    });

    it("should split by string", () => {
        runTestSet('public function main(sstr: String): List<String> { return sstr.split<String>(""); }', [['""', 'List<String>{ "" }'], ['"abc"', 'List<String>{ "a", "b", "c" }']], []);

        runTestSet('public function main(sstr: String): List<String> { return sstr.split<String>("###"); }', [['""', 'List<String>{ "" }'], ['"abc"', 'List<String>{ "abc" }'], ['"abc###"', 'List<String>{ "abc", "" }'], ['"###"', 'List<String>{ "", "" }'], ['"###def"', 'List<String>{ "", "def" }'], ['"123###def"', 'List<String>{ "123", "def" }'], ['"###abc###"', 'List<String>{ "", "abc", "" }'], ['"###abc###123"', 'List<String>{ "", "abc", "123" }'], ['"######123"', 'List<String>{ "", "", "123" }'], ['"123###abc"', 'List<String>{ "123", "abc" }']], []);
    });

    it("should split by cregex", () => {
        runTestSet('public function main(sstr: String): List<String> { return sstr.split<Regex>(/[0-9]*/); }', [['""', 'List<String>{ "" }'], ['"abc"', 'List<String>{ "a", "b", "c" }']], []);

        runTestSet('public function main(sstr: String): List<String> { return sstr.split<Regex>(/"###"/); }', [['""', 'List<String>{ "" }'], ['"abc"', 'List<String>{ "abc" }'], ['"abc###"', 'List<String>{ "abc", "" }'], ['"###"', 'List<String>{ "", "" }'], ['"###def"', 'List<String>{ "", "def" }'], ['"123###def"', 'List<String>{ "123", "def" }'], ['"###abc###"', 'List<String>{ "", "abc", "" }'], ['"###abc###123"', 'List<String>{ "", "abc", "123" }'], ['"######123"', 'List<String>{ "", "", "123" }'], ['"123###abc"', 'List<String>{ "123", "abc" }']], []);
    });
});

describe("String split tests with WS management", () => {
    it("should split and discard empty", () => {
        runTestSet('public function main(sstr: String): List<String> { return sstr.split<String>("###", dropempty = true); }', [['""', 'List<String>{ }'], ['" abc "', 'List<String>{ " abc " }'], ['"abc###"', 'List<String>{ "abc" }'], ['"###"', 'List<String>{ }'], ['" ###def"', 'List<String>{ " ", "def" }'], ['"123###def"', 'List<String>{ "123", "def" }'], ['"###abc###"', 'List<String>{ "abc" }'], ['"###abc###123"', 'List<String>{ "abc", "123" }'], ['"######123"', 'List<String>{ "123" }'], ['"123###abc"', 'List<String>{ "123", "abc" }'], ['"  ### "', 'List<String>{ "  ", " " }']], []);
    });
    
    it("should split and trim", () => {
        runTestSet('public function main(sstr: String): List<String> { return sstr.split<String>("###", trim = true); }', [['""', 'List<String>{ "" }'], ['" abc "', 'List<String>{ "abc" }'], ['"abc ### ### def "', 'List<String>{ "abc", "", "def" }']], []);
    });

    it("should split, trim, and discard empty", () => {
        runTestSet('public function main(sstr: String): List<String> { return sstr.split<String>("###", trim = true, dropempty = true); }', [['""', 'List<String>{ }'], ['" abc "', 'List<String>{ "abc" }'], ['"abc ### ### def "', 'List<String>{ "abc", "def" }'], ['"### abc ###"', 'List<String>{ "abc" }']], []);
    });
});

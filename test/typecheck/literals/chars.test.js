"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- CChar", () => {
    it("should check simple chars", function () {
        checkTestExp("c'x'", "CChar");
        checkTestExp("c' '", "CChar");
        
    });

    it("should check escaped chars", function () {
        checkTestExp("c'%x59;'", "CChar");
        checkTestExp("c'%%;'", "CChar");
        checkTestExp("c'%;'", "CChar");
    });

    it("should fail not single char", function () {
        checkTestExpError("c'xyz'", "CChar", 'Expected zero or one UnicodeChar, but found 3 characters');
        checkTestExpError("c'%%;%x59;'", "CChar", 'Expected zero or one UnicodeChar, but found 2 characters');
    });

    it("should fail bad escapes", function () {
        checkTestExpError("c'a%53'", "CChar", "Escape sequence is missing terminal ';'",);
        checkTestExpError("c'a%bob;'", "CChar", "Invalid escape sequence -- unknown escape name 'bob'");

        checkTestExpError("c'%x1f335;'", "CChar", "Invalid hex escape sequence");
    });
});

describe ("Checker -- UnicodeChar", () => {
    it("should check simple uchars", function () {
        checkTestExp('c"a"', "UnicodeChar");
        checkTestExp('c"🌵"', "UnicodeChar");
        checkTestExp('c" "', "UnicodeChar");
    });

    it("should check escaped strings", function () {
        checkTestExp('c"%x59;"', "UnicodeChar");
        checkTestExp('c"%x1f335;"', "UnicodeChar");
        checkTestExp('c"%%;"', "UnicodeChar");
        checkTestExp('c"%;"', "UnicodeChar");
    });

    it("should fail not single char", function () {
        checkTestExpError('c"abc"', "UnicodeChar", 'Expected zero or one UnicodeChar, but found 3 characters');
        checkTestExpError('c"%%;%x59;"', "UnicodeChar", 'Expected zero or one UnicodeChar, but found 2 characters');
    });

    it("should fail bad escapes", function () {
        checkTestExpError('c"a%53"', "UnicodeChar", "Escape sequence is missing terminal ';'");
        checkTestExpError('c"a%bob;"', "UnicodeChar", "Invalid escape sequence -- unknown escape name 'bob'");
    });
});

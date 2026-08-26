"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- CChar", () => {
    it("should parse simple cchars", function () {
        parseTestExp("c'a'", undefined, "CChar");
        parseTestExp("c'b'", undefined, "CChar");

        parseTestExp("c'%n;'", undefined, "CChar");
    });

    it("should fail invalid cchars", function () {
        parseTestExpError("c'", "Unterminated CChar literal", "CChar");
        parseTestExpError("c''", "Empty CChar literal", "CChar");
        parseTestExpError("c'🌵'", "Invalid character in CChar literal", "CChar");
    });
});

describe ("Parser -- Char", () => {
    it("should parse simple uchars", function () {
        parseTestExp('c"a"', undefined, "UnicodeChar");
        parseTestExp('c"b"', undefined, "UnicodeChar");

        parseTestExp('c"🌵"', undefined, "UnicodeChar");
        parseTestExp('c"%%;"', undefined, "UnicodeChar");
    });

    it("should fail invalid uchars", function () {
        parseTestExpError('c"', "Unterminated UnicodeChar literal", "UnicodeChar");
        parseTestExpError('c""', "Empty UChar literal", "UnicodeChar");
    });
});

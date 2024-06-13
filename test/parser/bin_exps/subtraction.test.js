"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat subtraction", () => {
    it("should parse simple nats", function () {
        parseTestExp("1n - 1n", undefined, "Nat");
        parseTestExp("2n - +2n", undefined, "Nat");
        parseTestExp("5n - 1n", undefined, "Nat");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2n-3n", 'Expected ";" but got "-3n" when parsing "line statement"', "Nat");
    });
});


describe ("Parser -- BigInt subtraction", () => {
    it("should parse simple nats", function () {
        parseTestExp("0I - 1I", undefined, "BigInt");
        parseTestExp("+2I - -2I", undefined, "BigInt");
        parseTestExp("1I - +3I", undefined, "BigInt");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2I-3I", 'Expected ";" but got "-3I" when parsing "line statement"', "BigInt");
    });
});


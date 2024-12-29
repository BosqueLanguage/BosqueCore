"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat division", () => {
    it("should parse simple nats", function () {
        parseTestExp("1n // 1n", undefined, "Nat");
        parseTestExp("2n // +2n", undefined, "Nat");
        parseTestExp("5n // 1n", undefined, "Nat");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2n//3n", 'Invalid characters in (or empty) Regex literal', "Nat");
    });
});


describe ("Parser -- BigInt division", () => {
    it("should parse simple nats", function () {
        parseTestExp("0I // 1I", undefined, "BigInt");
        parseTestExp("+2I // -2I", undefined, "BigInt");
        parseTestExp("1I // +3I", undefined, "BigInt");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2I//3I", 'Invalid characters in (or empty) Regex literal', "BigInt");
    });
});


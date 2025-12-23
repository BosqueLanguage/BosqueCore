"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat multiplication", () => {
    it("should parse simple nats", function () {
        parseTestExp("1n * 1n", undefined, "Nat");
        parseTestExp("2n * +2n", undefined, "Nat");
        parseTestExp("5n * 1n", undefined, "Nat");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2n*3n", 'Unrecognized token', "Nat");
    });
});


describe ("Parser -- ChkInt multiplication", () => {
    it("should parse simple chkint", function () {
        parseTestExp("0I * 1I", undefined, "ChkInt");
        parseTestExp("+2I * -2I", undefined, "ChkInt");
        parseTestExp("1I * +3I", undefined, "ChkInt");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2I*3I", 'Unrecognized token', "ChkInt");
    });
});

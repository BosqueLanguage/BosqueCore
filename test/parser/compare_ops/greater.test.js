"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- basic >", () => {
    it("should compare simple nats", function () {
        parseTestExp("0n > 1n", undefined, "Bool");
        parseTestExp("+2n > 2n", undefined, "Bool");
        parseTestExp("1n > +3n", undefined, "Bool");
    });

    it("should fail stuck operator", function () {
        parseTestExpError("2n>3n", 'Expected ";" but got ">" when parsing "line statement"', "Nat");
    });
});


describe ("Parser -- basic >=", () => {
    it("should compare simple nats", function () {
        parseTestExp("0n >= 1n", undefined, "Bool");
        parseTestExp("+2n >= 2n", undefined, "Bool");
        parseTestExp("1n >= +3n", undefined, "Bool");
    });

    it("should fail stuck operator", function () {
        parseTestExpError("2n>=3n", 'Expected ";" but got ">" when parsing "line statement"', "Nat");
    });
});


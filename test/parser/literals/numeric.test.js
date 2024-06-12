"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat", () => {
    it("should parse simple nats", function () {
        parseTestExp("0n", undefined, "Nat");
        parseTestExp("+2n", undefined, "Nat");
        parseTestExp("+0n", undefined, "Nat");
    });
});

describe ("Parser -- Int", () => {
    it("should parse simple ints", function () {
        parseTestExp("0i", undefined, "Int");
        parseTestExp("+2i", undefined, "Int");
        parseTestExp("-2i", undefined, "Int");
    });
});

describe ("Parser -- BigNat", () => {
    it("should parse simple big nats", function () {
        parseTestExp("0N", undefined, "BigNat");
        parseTestExp("+2N", undefined, "BigNat");
    });
});

describe ("Parser -- BigInt", () => {
    it("should parse simple big ints", function () {
        parseTestExp("0I", undefined, "BigInt");
        parseTestExp("+2I", undefined, "BigInt");
        parseTestExp("-2I", undefined, "BigInt");
    });
});

describe ("Parser -- Float", () => {
    it("should parse simple floats", function () {
        parseTestExp("0.0f", undefined, "Float");
        parseTestExp("+2.0f", undefined, "Float");
        parseTestExp("-2.0f", undefined, "Float");
    });

    it("should fail missing .x float", function () {
        parseTestExpError("1f", "Un-annotated numeric literals are not supported", "Float");
    });
});

describe ("Parser -- Decimal", () => {
    it("should parse simple decimals", function () {
        parseTestExp("0.0d", undefined, "Decimal");
        parseTestExp("+2.0d", undefined, "Decimal");
        parseTestExp("-2.0d", undefined, "Decimal");
    });

    it.skip("should fail missing .x decimal", function () {
        parseTestExpError("0d", "Un-annotated numeric literals are not supported", "Decimal");
    });
});


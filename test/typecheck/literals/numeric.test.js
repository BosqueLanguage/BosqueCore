"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Nat", () => {
    it("should check simple nats", function () {
        checkTestExp("0n", "Nat");
        checkTestExp("+2n", "Nat");
    });

    it("should fail simple nats", function () {
        checkTestExpError("0n", "Int", "Expected a return value of type Int but got Nat");
        checkTestExpError("-20n", "Nat", "Nat literal cannot be negative");
    });
});

describe ("Checker -- Int", () => {
    it("should check simple ints", function () {
        checkTestExp("0i", "Int");
        checkTestExp("+2i", "Int");
        checkTestExp("-2i", "Int");
    });

    it("should fail simple ints", function () {
        checkTestExpError("0n", "None", "Expected a return value of type None but got Nat");
    });
});

describe ("Checker -- BigNat", () => {
    it("should check simple big nats", function () {
        checkTestExp("0N", "BigNat");
        checkTestExp("+2N", "BigNat");
    });

    it("should fail simple big nats", function () {
        checkTestExpError("0N", "Nat", "Expected a return value of type Nat but got BigNat");
        checkTestExpError("-20N", "BigNat", "BigNat literal cannot be negative");
    });
});

describe ("Checker -- BigInt", () => {
    it("should check simple big ints", function () {
        checkTestExp("0I", "BigInt");
        checkTestExp("+2I", "BigInt");
        checkTestExp("-2I", "BigInt");
    });

    it("should fail simple big nats", function () {
        checkTestExpError("0N", "Nat", "Expected a return value of type Nat but got BigNat");
    });
});

describe ("Checker -- Float", () => {
    it("should check simple floats", function () {
        checkTestExp("0.0f", "Float");
        checkTestExp("+2.5f", "Float");
        checkTestExp("-2.0f", "Float");
    });

    it("should fail simple float", function () {
        checkTestExpError("1.0f", "Nat", "Expected a return value of type Nat but got Float");
    });
});

describe ("Checker -- Decimal", () => {
    it("should parse simple decimals", function () {
        checkTestExp("0.0d", "Decimal");
        checkTestExp("+2.3d", "Decimal");
        checkTestExp("-2.0d", "Decimal");
    });

    it("should fail simple decimal", function () {
        checkTestExpError("1.0d", "None", "Expected a return value of type None but got Decimal");
    });
});


describe ("Checker -- Rational", () => {
    it("should parse simple rationals", function () {
        checkTestExp("0R", "Rational");
        checkTestExp("+2/3R", "Rational");
    });

    it("should fail simple rational", function () {
        checkTestExpError("1R", "None", "Expected a return value of type None but got Rational");
    });
});

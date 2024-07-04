"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat", () => {
    it("should parse simple nats", function () {
        parseTestExp("0n", undefined, "Nat");
        parseTestExp("+2n", undefined, "Nat");
        parseTestExp("+0n", undefined, "Nat");
    });

    it("should fail stacked signs", function () {
        parseTestExpError("++5n", "Redundant sign", "Nat");
    });
});

describe ("Parser -- Int", () => {
    it("should parse simple ints", function () {
        parseTestExp("0i", undefined, "Int");
        parseTestExp("+2i", undefined, "Int");
        parseTestExp("-2i", undefined, "Int");
    });

    it("should fail stacked signs", function () {
        parseTestExpError("--5n", "Redundant sign", "Int");
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

    it("should fail stacked signs", function () {
        parseTestExpError("+-1.0f", "Redundant sign", "Float");
    });
});

describe ("Parser -- Decimal", () => {
    it("should parse simple decimals", function () {
        parseTestExp("0.0d", undefined, "Decimal");
        parseTestExp("+2.0d", undefined, "Decimal");
        parseTestExp("-2.0d", undefined, "Decimal");
    });

    it("should fail missing .x decimal", function () {
        parseTestExpError("0d", "Un-annotated numeric literals are not supported", "Decimal");
    });
});

describe ("Parser -- Rational", () => {
    it("should parse simple rationals", function () {
        parseTestExp("0R", undefined, "Rational");
        parseTestExp("1/2R", undefined, "Rational");
        parseTestExp("-3/4R", undefined, "Rational");
    });

    it("should fail zero denom rational", function () {
        parseTestExpError("1/0R", "Zero denominator in rational number", "Rational");
    });

    it("should fail zero denom rational", function () {
        parseTestExpError("1/0(Foo)", "Zero denominator in rational number", "Rational");
    });
});

describe ("Parser -- DecimalDegree", () => {
    it("should parse simple decimal degree", function () {
        parseTestExp("0.0dd", undefined, "DecimalDegree");
        parseTestExp("200.123dd", undefined, "DecimalDegree");
        parseTestExp("+0.123dd", undefined, "DecimalDegree");
    });

    it("should fail missing .x", function () {
        parseTestExpError("1dd", "Un-annotated numeric literals are not supported", "DecimalDegree");
    });
});

describe ("Parser -- Lat/Long", () => {
    it("should parse simple lat/long", function () {
        parseTestExp("2.0lat-80.123long", undefined, "LatLongCoordinate");
        parseTestExp("-2.0lat+80.123long", undefined, "LatLongCoordinate");
    });

    it("should fail missing long", function () {
        parseTestExpError("2.0lat", "Un-annotated numeric literals are not supported", "LatLongCoordinate");
    });

    it("should fail double --", function () {
        parseTestExpError("-2.0lat--80.123long", "Redundant sign", "LatLongCoordinate");
    });
});

describe ("Parser -- Complex", () => {
    it("should parse simple complex", function () {
        parseTestExp("0.0+0.0j", undefined, "Complex");
        parseTestExp("-2.0-0.5j", undefined, "Complex");
    });

    it("should fail bad imag", function () {
        parseTestExpError("-2.0+5j", "Un-annotated numeric literals are not supported", "Complex");
    });

    it("should fail missing real", function () {
        parseTestExpError("-0.5j", "Un-annotated numeric literals are not supported", "Complex");
    });

    it("should fail missing imag", function () {
        parseTestExpError("-2.0", "Un-annotated numeric literals are not supported", "Complex");
    });
});

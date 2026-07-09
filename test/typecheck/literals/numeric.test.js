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

describe ("Checker -- ChkNat", () => {
    it("should check simple big nats", function () {
        checkTestExp("0N", "ChkNat");
        checkTestExp("+2N", "ChkNat");
    });

    it("should fail simple big nats", function () {
        checkTestExpError("0N", "Nat", "Expected a return value of type Nat but got ChkNat");
        checkTestExpError("-20N", "ChkNat", "ChkNat literal cannot be negative");
    });
});

describe ("Checker -- ChkInt", () => {
    it("should check simple big ints", function () {
        checkTestExp("0I", "ChkInt");
        checkTestExp("+2I", "ChkInt");
        checkTestExp("-2I", "ChkInt");
    });

    it("should fail simple big ints", function () {
        checkTestExpError("0I", "Int", "Expected a return value of type Int but got ChkInt");
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

describe ("Checker -- Decimal Degree", () => {
    it("should parse simple decimal degree", function () {
        checkTestExp("0.0dd", "DecimalDegree");
        checkTestExp("200.123dd", "DecimalDegree");
        checkTestExp("+0.123dd", "DecimalDegree");
        checkTestExp("360.0dd", "DecimalDegree");
        checkTestExp("-360.0dd", "DecimalDegree");
    });

    it("should fail simple decimal degree", function () {
        checkTestExpError("0.0dd", "None", "Expected a return value of type None but got DecimalDegree");
    });

    it("should fail too overflow pos", function () {
        checkTestExpError("360.1dd", "DecimalDegree", "Invalid DecimalDegree literal");
    });

    it("should fail too overflow neg", function () {
        checkTestExpError("-360.1dd", "None", "Invalid DecimalDegree literal");
    });
});

describe ("Checker -- Lat/Long", () => {
    it("should parse simple lat/long", function () {
        checkTestExp("2.0lat-80.123long", "LatLongCoordinate");
        checkTestExp("-2.0lat+80.123long", "LatLongCoordinate");
        checkTestExp("-180.0lat-90.0long", "LatLongCoordinate");
        checkTestExp("+180.0lat+90.0long", "LatLongCoordinate");
    });

    it("should fail simple LatLong", function () {
        checkTestExpError("2.0lat-80.123long", "DecimalDegree", "Expected a return value of type DecimalDegree but got LatLongCoordinate");
    });

    it("should fail too overflow pos lat", function () {
        checkTestExpError("180.1lat-90.0long", "LatLongCoordinate", "Invalid Latitude value");
    });

    it("should fail too overflow neg lat", function () {
        checkTestExpError("-180.1lat-90.0long", "LatLongCoordinate", "Invalid Latitude value");
    });

    it("should fail too overflow pos long", function () {
        checkTestExpError("-180.0lat+91.0long", "LatLongCoordinate", "Invalid Longitude value");
    });

    it("should fail too overflow neg long", function () {
        checkTestExpError("-180.0lat-100.0long", "LatLongCoordinate", "Invalid Longitude value");
    });
});

describe ("Checker -- Complex", () => {
    it("should parse simple complex", function () {
        checkTestExp("0.0+0.0j", "Complex");
        checkTestExp("-2.0-0.5j", "Complex");
    });

    it("should fail simple complex", function () {
        checkTestExpError("-2.0-0.5j", "Float", "Expected a return value of type Float but got Complex");
    });
});

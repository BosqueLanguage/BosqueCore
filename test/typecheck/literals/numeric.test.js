"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat", () => {
    it("should check simple nats", function () {
        checkTestExp("0n", "Nat");
        checkTestExp("+2n", "Nat");
    });

    it("should fail simple nats", function () {
        checkTestExpError("0n", "Int", "Expected a return value of type Int but got Nat");
        checkTestExpError("-20n", "Nat", "Nat literal cannot be negative");
    });
});

describe ("Parser -- Int", () => {
    it("should check simple ints", function () {
        checkTestExp("0i", "Int");
        checkTestExp("+2i", "Int");
        checkTestExp("-2i", "Int");
    });

    it("should fail simple ints", function () {
        checkTestExpError("0n", "None", "Expected a return value of type None but got Nat");
    });
});

describe ("Parser -- BigNat", () => {
    it("should check simple big nats", function () {
        checkTestExp("0N", "BigNat");
        checkTestExp("+2N", "BigNat");
    });

    it("should fail simple big nats", function () {
        checkTestExpError("0N", "Nat", "Expected a return value of type Nat but got BigNat");
        checkTestExpError("-20N", "BigNat", "BigNat literal cannot be negative");
    });
});

describe ("Parser -- BigInt", () => {
    it("should check simple big ints", function () {
        checkTestExp("0I", "BigInt");
        checkTestExp("+2I", "BigInt");
        checkTestExp("-2I", "BigInt");
    });

    it("should fail simple big nats", function () {
        checkTestExpError("0N", "Nat", "Expected a return value of type Nat but got BigNat");
    });
});

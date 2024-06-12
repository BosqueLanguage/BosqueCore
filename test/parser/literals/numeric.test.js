"use strict";

import { parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat", () => {
    it("should parse simple nats", function () {
        parseTestExp("0n", undefined, "Nat");
        parseTestExp("+2n", undefined, "Nat");
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

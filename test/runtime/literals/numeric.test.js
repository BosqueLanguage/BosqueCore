"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- Nat", () => {
    it("should exec simple nats", function () {
        runMainCode("public function main(): Nat { return 0n; }", [0n, "Nat"]);
        runMainCode("public function main(): Nat { return +2n; }", [2n, "Nat"]);
    });
});

describe ("Exec -- Int", () => {
    it("should check simple ints", function () {
        runMainCode("public function main(): Int { return 0i; }", [0n, "Int"]);
        runMainCode("public function main(): Int { return +2i; }", [2n, "Int"]);
        runMainCode("public function main(): Int { return -2i; }", [-2n, "Int"]);
    });
});

describe ("Exec -- BigNat", () => {
    it("should exec simple big nats", function () {
        runMainCode("public function main(): BigNat { return 0N; }", [0n, "BigNat"]);
        runMainCode("public function main(): BigNat { return +2N; }", [2n, "BigNat"]);
    });
});

describe ("Exec -- BigInt", () => {
    it("should exec simple big ints", function () {
        runMainCode("public function main(): BigInt { return 0I; }", [0n, "BigInt"]);
        runMainCode("public function main(): BigInt { return +2I; }", [2n, "BigInt"]);
        runMainCode("public function main(): BigInt { return -2I; }", [-2n, "BigInt"]);
    });
});

describe ("Exec -- Float", () => {
    it("should exec simple floats", function () {
        runMainCode("public function main(): Float { return 0.0f; }", [0.0, "Float"]);
        runMainCode("public function main(): Float { return 1.0f; }", [1.0, "Float"]);
        runMainCode("public function main(): Float { return -2.0f; }", [-2.0, "Float"]);
    });
});


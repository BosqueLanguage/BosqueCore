"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe("CPP Emit Evaluate -- Nat", () => {
    it("should exec simple nats", function () {
        runMainCode("public function main(): Nat { return 0n; }", "0_n");
        runMainCode("public function main(): Nat { return +2n; }", "2_n");
    });
});

describe("CPP Emit Evaluate -- Int", () => {
    it("should check simple ints", function () {
        runMainCode("public function main(): Int { return 0i; }", "0_i");
        runMainCode("public function main(): Int { return +2i; }", "2_i");
        runMainCode("public function main(): Int { return -2i; }", "-2_i");
    });
});

describe("CPP Emit Evaluate -- BigNat", () => {
    it("should exec simple big nats", function () {
        runMainCode("public function main(): BigNat { return 0N; }", "0_N");
        runMainCode("public function main(): BigNat { return +2N; }", "2_N");
    });
});

describe("CPP Emit Evaluate -- BigInt", () => {
    it("should exec simple big ints", function () {
        runMainCode("public function main(): BigInt { return 0I; }", "0_I");
        runMainCode("public function main(): BigInt { return +2I; }", "2_I");
        runMainCode("public function main(): BigInt { return -2I; }", "-2_I");
    });
});

describe("CPP Emit Evaluate -- Float", () => {
    it("should exec simple floats", function () {
        runMainCode("public function main(): Bool { return 0.0f < 0.1f; }", "true");
        runMainCode("public function main(): Bool { return 1.0f > 0.9f; }", "true");
        runMainCode("public function main(): Bool { return -2.0f < -1.9f; }", "true");
    });
});
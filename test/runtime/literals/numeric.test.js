"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- Nat", () => {
    it("should exec simple nats", function () {
        runMainCode("public function main(): Nat { return 0n; }", "0n");
        runMainCode("public function main(): Nat { return +2n; }", "2n");
    });
});

describe ("Exec -- Int", () => {
    it("should check simple ints", function () {
        runMainCode("public function main(): Int { return 0i; }", "0i");
        runMainCode("public function main(): Int { return +2i; }", "2i");
        runMainCode("public function main(): Int { return -2i; }", "-2i");
    });
});

describe ("Exec -- BigNat", () => {
    it("should exec simple big nats", function () {
        runMainCode("public function main(): BigNat { return 0N; }", "0N");
        runMainCode("public function main(): BigNat { return +2N; }", "2N");
    });
});

describe ("Exec -- BigInt", () => {
    it("should exec simple big ints", function () {
        runMainCode("public function main(): BigInt { return 0I; }", "0I");
        runMainCode("public function main(): BigInt { return +2I; }", "2I");
        runMainCode("public function main(): BigInt { return -2I; }", "-2I");
    });
});

describe ("Exec -- Float", () => {
    it("should exec simple floats", function () {
        runMainCode("public function main(): Float { return 0.0f; }", "0.0f");
        runMainCode("public function main(): Float { return 1.0f; }", "1.0f");
        runMainCode("public function main(): Float { return -2.0f; }", "-2.0f");
    });
});


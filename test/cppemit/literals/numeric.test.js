"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Nat", () => {
    it("should emit simple nats", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 0n; }", "Nat Mainᕒmain() { return 0_n; }");
        checkTestEmitMainFunction("public function main(): Nat { return +2n; }", "Nat Mainᕒmain() { return 2_n; }");
    });
});

describe ("CPPEmit -- Int", () => {
    it("should emit simple ints", function () {
        checkTestEmitMainFunction("public function main(): Int { return 0i; }", "Int Mainᕒmain() { return 0_i; }");
        checkTestEmitMainFunction("public function main(): Int { return +2i; }", "Int Mainᕒmain() { return 2_i; }");
        checkTestEmitMainFunction("public function main(): Int { return -2i; }", "Int Mainᕒmain() { return -2_i; }");
    });
});

describe ("CPPEmit -- ChkNat", () => {
    it("should emit simple chk nats", function () {
        checkTestEmitMainFunction("public function main(): ChkNat { return 0N; }", "ChkNat Mainᕒmain() { return 0_N; }");
        checkTestEmitMainFunction("public function main(): ChkNat { return +2N; }", "ChkNat Mainᕒmain() { return 2_N; }");
    });
});

describe ("CPPEmit -- ChkInt", () => {
    it("should emit simple chk ints", function () {
        checkTestEmitMainFunction("public function main(): ChkInt { return 0I; }", "ChkInt Mainᕒmain() { return 0_I; }");
        checkTestEmitMainFunction("public function main(): ChkInt { return +2I; }", "ChkInt Mainᕒmain() { return 2_I; }");
        checkTestEmitMainFunction("public function main(): ChkInt { return -2I; }", "ChkInt Mainᕒmain() { return -2_I; }");
    });
});

describe ("CPPEmit -- Float", () => {
    it("should emit simple floats", function () {
        checkTestEmitMainFunction("public function main(): Float { return 0.0f; }", "Float Mainᕒmain() { return 0.0_f; }");
        checkTestEmitMainFunction("public function main(): Float { return 1.0f; }", "Float Mainᕒmain() { return 1.0_f; }");
        checkTestEmitMainFunction("public function main(): Float { return -2.0f; }", "Float Mainᕒmain() { return -2.0_f; }");
    });
});


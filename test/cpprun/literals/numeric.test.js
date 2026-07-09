"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Nat", () => {
    it("should exec simple nats", function () {
        runTestSet("public function main(): Nat { return 0n; }", [[undefined, "0n"]], []);
        runTestSet("public function main(): Nat { return +2n; }", [[undefined, "2n"]], []);
    });
});

describe ("CPPExec -- Int", () => {
    it("should exec simple ints", function () {
        runTestSet("public function main(): Int { return 0i; }", [[undefined, "0i"]], []);
        runTestSet("public function main(): Int { return +2i; }", [[undefined, "2i"]], []);
        runTestSet("public function main(): Int { return -2i; }", [[undefined, "-2i"]], []);
    });
});

describe ("CPPExec -- ChkNat", () => {
    it("should exec simple chk nats", function () {
        runTestSet("public function main(): ChkNat { return 0N; }", [[undefined, "0N"]], []);
        runTestSet("public function main(): ChkNat { return +2N; }", [[undefined, "2N"]], []);
    });
});

describe ("CPPExec -- ChkInt", () => {
    it("should exec simple chk ints", function () {
        runTestSet("public function main(): ChkInt { return 0I; }", [[undefined, "0I"]], []);
        runTestSet("public function main(): ChkInt { return +2I; }", [[undefined, "2I"]], []);
        runTestSet("public function main(): ChkInt { return -2I; }", [[undefined, "-2I"]], []);
    });
});

describe ("CPPExec -- Float", () => {
    it("should exec simple floats", function () {
        runTestSet("public function main(): Float { return 0.0f; }", [[undefined, "0.0f"]], []);
        runTestSet("public function main(): Float { return 1.0f; }", [[undefined, "1.0f"]], []);
        runTestSet("public function main(): Float { return -2.0f; }", [[undefined, "-2.0f"]], []);
    });
});


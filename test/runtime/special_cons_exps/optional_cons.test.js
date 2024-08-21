"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

/*
describe ("Checker -- Special Constructor Optional", () => {
    it("should check none with simple infer", function () {
        runMainCode("public function main(): None { return none; }", [null, "None"]);
        runMainCode("public function main(): Int? { return none", "Int?");
    });

    it("should check some with simple infer", function () {
        runMainCode("some(3i)", "Some<Int>");
        runMainCode("some(3i)", "Int?");
    });
});

describe ("Checker -- Special Constructor Result", () => {
    it("should check ok with simple infer", function () {
        runMainCode("ok(3i)", "Result<Int, Bool>::Ok");
        runMainCode("ok(3i)", "Result<Int, Bool>");
    });

    it("should check err with simple infer", function () {
        runMainCode("err(true)", "Result<Int, Bool>::Err");
        runMainCode("err(false)", "Result<Int, Bool>");
    });
});

describe ("Checker -- Special Constructor infer in if-else and assign positions", () => {
    it("should check with if-else", function () {
        runMainCode("if(true) then ok(3i) else err(false)", "Result<Int, Bool>");
        runMainCode("if(false) then none else some(3i)", "Int?");
    });
});
*/
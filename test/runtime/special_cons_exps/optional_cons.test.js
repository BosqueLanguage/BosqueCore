"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Special Constructor Optional", () => {
    it("should check none with simple infer", function () {
        runMainCode("public function main(): None { return none; }", [null, "None"]);
        runMainCode("public function main(): Int { let x: Some<Int> = some(3i); return x.value; }", [3n, "Int"]);
        runMainCode("public function main(): Int { let x: Int? = some(3i); return x@some; }", [3n, "Int"]);
    });
});

describe ("Checker -- Special Constructor Result", () => {
    it("should check ok with simple infer", function () {
        runMainCode("public function main(): Int { let x: Result<Int, Bool>::Ok = ok(3i); return x.value; }", [3n, "Int"]);
        runMainCode("public function main(): Int { let x: Result<Int, Bool> = ok(3i); return x@ok; }", [3n, "Int"]);
    });

    it("should check err with simple infer", function () {
        runMainCode("public function main(): Bool { let x: Result<Int, Bool>::Err = err(true); return x.info; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { let x: Result<Int, Bool> = err(true); return x@err; }", [true, "Bool"]);
    });
});

/*
describe ("Checker -- Special Constructor infer in if-else and assign positions", () => {
    it("should check with if-else", function () {
        runMainCode("if(true) then ok(3i) else err(false)", "Result<Int, Bool>");
        runMainCode("if(false) then none else some(3i)", "Int?");
    });
});
*/
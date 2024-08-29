"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Special Constructor Optional", () => {
    it("should exec none with simple infer", function () {
        runMainCode("public function main(): None { return none; }", [null, "None"]);
        runMainCode("public function main(): Int { let x: Some<Int> = some(3i); return x.value; }", [3n, "Int"]);
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); return x@some; }", [3n, "Int"]);
    });
});

describe ("Exec -- Special Constructor Result", () => {
    it("should exec ok with simple infer", function () {
        runMainCode("public function main(): Int { let x: Result<Int, Bool>::Ok = ok(3i); return x.value; }", [3n, "Int"]);
        runMainCode("public function main(): Int { let x: Result<Int, Bool> = ok(3i); return x@ok; }", [3n, "Int"]);
    });

    it("should exec err with simple infer", function () {
        runMainCode("public function main(): Bool { let x: Result<Int, Bool>::Err = fail(true); return x.info; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { let x: Result<Int, Bool> = fail(true); return x@fail; }", [true, "Bool"]);
    });
});

describe ("Exec -- Special Constructor infer in if-else and assign positions", () => {
    it("should exec some/none with if-else", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = if(true) then some(3i) else none; return x@some; }", [3n, "Int"]);
        runMainCode("public function main(): None { let x: Option<Int> = if(false) then some(3i) else none; return x@!some; }", [null, "None"]);
    });

    it("should exec ok/err with if-else", function () {
        runMainCode("public function main(): Int { let x: Result<Int, Bool> = if(true) then ok(3i) else err(true); return x@ok; }", [3n, "Int"]);
        runMainCode("public function main(): Bool { let x: Result<Int, Bool> = if(false) then ok(3i) else err(true); return x@!ok; }", [true, "Bool"]);
    });
});

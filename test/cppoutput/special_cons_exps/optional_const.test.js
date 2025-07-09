"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Special Constructor infer in if-else and assign positions", () => {
    it("should exec some/none with if-else", function () {
        runMainCode("public function main(): Int { let x: Option<Int> = if(true) then some(3i) else none; return x@some; }", "3_i");
        runMainCode("public function main(): Bool { let x: Option<Int> = if(false) then some(3i) else none; return x?!some; }", "true");
    });

    /*
    it("should exec ok/fail with if-else", function () {
        runMainCode("public function main(): Int { let x: Result<Int, Bool> = if(true) then ok(3i) else fail(true); return x@ok; }", "3i");
        runMainCode("public function main(): Bool { let x: Result<Int, Bool> = if(false) then ok(3i) else fail(true); return x@!ok; }", "true");
    });
    */
});

describe ("Exec -- Special Constructor Optional", () => {
    it("should exec none with simple infer", function () {
        runMainCode("public function main(): Int { let x: Some<Int> = some(3i); return x.value; }", "3_i");
        runMainCode("public function main(): Int { let x: Option<Int> = some(3i); return x@some; }", "3_i");
    });
});

/*
describe ("Exec -- Special Constructor Result", () => {
    it("should exec ok with simple infer", function () {
        runMainCode("public function main(): Int { let x: Result<Int, Bool>::Ok = ok(3i); return x.value; }", "3i");
        runMainCode("public function main(): Int { let x: Result<Int, Bool> = ok(3i); return x@ok; }", "3i");
    });

    it("should exec fail with simple infer", function () {
        runMainCode("public function main(): Bool { let x: Result<Int, Bool>::Fail = fail(true); return x.info; }", "true");
        runMainCode("public function main(): Bool { let x: Result<Int, Bool> = fail(true); return x@fail; }", "true");
    });
});
*/
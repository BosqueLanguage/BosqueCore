"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Special Constructor Optional", () => {
    it("should smt exec none with simple infer", function () {
        runishMainCodeUnsat("public function main(): Int { let x: Some<Int> = some(3i); return x.value; }", "(assert (not (= Main@main 3)))");
        runishMainCodeUnsat("public function main(): Int { let x: Option<Int> = some(3i); return x@some; }", "(assert (not (= Main@main (@Result-ok 3))))");
    });
});


"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- Constructable Constructor (Option)", () => {
    it("should smt exec option constructors", function () {
        runishMainCodeUnsat("public function main(): Int { return Some<Int>{2i}.value; }", "(assert (not (= 2 Main@main)))");
    });
});

/*
describe ("Exec -- Constructable Constructor (Result)", () => {
    it("should exec result constructors", function () {
        runMainCode("public function main(): Int { return Result<Int, Bool>::Ok{2i}.value; }", "2i");
        runMainCode("public function main(): Bool { return Result<Int, Bool>::Fail{false}.info; }", "false");
    });
});

describe ("Exec -- Constructable Constructor (MapEntry)", () => {
    it("should exec entry constructors", function () {
        runMainCode("public function main(): Int { return MapEntry<Int, Bool>{2i, true}.key; }", "2i");
        runMainCode("public function main(): Bool { return MapEntry<Int, Bool>{2i, true}.value; }", "true");
    });
});
*/

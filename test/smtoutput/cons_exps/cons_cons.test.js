"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT evaluate -- Constructable Constructor (Option)", () => {
    it("should exec option constructors", function () {
        runishMainCodeUnsat("public function main(): Int { return Some<Int>{2i}.value; }", "(assert (not (= Main@main 2)))");
    });
});


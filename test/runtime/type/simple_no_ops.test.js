"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- type decl of bool", () => {
    it("should exec bool type decl", function () {
        runMainCode("type Flag = Bool; public function main(): Bool { let e = true<Flag>; return e.value; }", [true, "Bool"]); 
    });
});

describe ("Exec -- type decl of number", () => {
    it("should exec numeric type decls", function () {
        runMainCode('type NVal = Int; public function main(): Int { let e = -2i<NVal>; return e.value; }', [-2n, "Int"]);
    });
});


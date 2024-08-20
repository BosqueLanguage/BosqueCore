"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- simple declare only", () => {
    it("should type simple declares", function () {
        runMainCode("public function main(): Int { var x: Int; return 0i; }", [0n, "Int"]);
        runMainCode("public function main(): Bool { var x: Bool; return true; }", [true, "Bool"]);
    });
});

describe ("Exec -- simple declare-assign only", () => {
    it("should type simple declare-assign", function () {
        runMainCode("public function main(): Int { var x: Int = 5i; return x; }", [5n, "Int"]);
        runMainCode("public function main(): Bool { let x: Bool = true; return x; }", [true, "Bool"]);
    });

    it("should type simple declare-assign infer type", function () {
        runMainCode("public function main(): Int { var x = 5i; return x; }", [5n, "Int"]);
        runMainCode("public function main(): Bool { let x = true; return x; }", [true, "Bool"]);
    });
});

describe ("Exec -- simple assign", () => {
    it("should type simple assign", function () {
        runMainCode("public function main(): Int { var x: Int = 5i; x = 2i; return x; }", [2n, "Int"]);
        runMainCode("public function main(): Int { var x: Int = 5i; x = 2i; x = 0i; return x; }", [0n, "Int"]);
    });

    it("should ignore assign", function () {
        runMainCode("public function main(): Int { _ = 2i; return 0i; }", [0n, "Int"]);
    });
});


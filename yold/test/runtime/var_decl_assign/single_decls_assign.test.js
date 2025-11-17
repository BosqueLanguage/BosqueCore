"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- simple declare only", () => {
    it("should exec simple declares", function () {
        runMainCode("public function main(): Int { var x: Int; return 0i; }", "0i");
        runMainCode("public function main(): Bool { var x: Bool; return true; }", "true");
    });
});

describe ("Exec -- simple declare-assign only", () => {
    it("should exec simple declare-assign", function () {
        runMainCode("public function main(): Int { var x: Int = 5i; return x; }", "5i");
        runMainCode("public function main(): Bool { let x: Bool = true; return x; }", "true");
    });

    it("should exec simple declare-assign infer type", function () {
        runMainCode("public function main(): Int { var x = 5i; return x; }", "5i");
        runMainCode("public function main(): Bool { let x = true; return x; }", "true");
    });
});

describe ("Exec -- simple assign", () => {
    it("should exec simple assign", function () {
        runMainCode("public function main(): Int { var x: Int = 5i; x = 2i; return x; }", "2i");
        runMainCode("public function main(): Int { var x: Int = 5i; x = 2i; x = 0i; return x; }", "0i");
    });

    it("should ignore assign", function () {
        runMainCode("public function main(): Int { _ = 2i; return 0i; }", "0i");
    });
});


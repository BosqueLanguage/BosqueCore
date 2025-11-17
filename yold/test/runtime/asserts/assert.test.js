"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- simple abort", () => {
    it("should exec simple abort", function () {
        runMainCode("public function main(): Int { if(false) { abort; } return 1i; }", "1i");

        runMainCodeError("public function main(): Int { if(true) { abort; } return 1i; }", "Error -- abort @ test.bsq:3");
    });
});

describe ("Exec -- simple assert", () => {
    it("should exec simple assert", function () {
        runMainCode("public function main(): Int { assert true; return 1i; }", "1i");
        runMainCode("public function main(): Int { assert debug false; return 1i; }", "1i");
    });

    it("should exec error assert", function () {
        runMainCodeError("public function main(): Int { assert 1i > (1i + 2i); return 1i; }", "Error -- 1i > (1i + 2i) @ test.bsq:3");
        runMainCodeError("public function main(): Int { assert test false; return 1i; }", "Error -- false @ test.bsq:3");
    });
});

describe ("Exec -- simple validate", () => {
    it("should exec simple validate", function () {
        runMainCode("public function main(): Int { validate true; return 1i; }", "1i");
    });

    it("should exec error validate", function () {
        runMainCodeError("public function main(): Int { validate 1i > (1i + 2i) || false; return 1i; }", "Error -- (1i > (1i + 2i)) || false @ test.bsq:3");
        runMainCodeError("public function main(): Int { validate['ec-0'] false; return 1i; }", "Error -- false['ec-0'] @ test.bsq:3");
    });
});


"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- NamespaceFunction Pre/Post", () => {
    it("should exec simple positional", function () {
        runMainCode("function foo(x: Int): Int requires x > 0i; { return 1i; } public function main(): Int { return foo(3i); }", "1i");
    });

    it("should exec simple (fail) positional", function () {
        runMainCodeError("function foo(x: Int): Int requires x > 0i; { return 1i; } public function main(): Int { return foo(0i); }", "Error -- x > 0i @ test.bsq:3");
    });
});

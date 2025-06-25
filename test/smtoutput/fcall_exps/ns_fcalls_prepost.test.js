"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- NamespaceFunction Pre/Post", () => {
    it("should smt exec simple precond", function () {
        runishMainCodeUnsat("function foo(x: Int): Int requires x > 0i; { return 1i; } public function main(a: Int): Int { return foo(a); }", "(assert (not (= (@Result-ok 1) (Main@main 5))))");
        runishMainCodeUnsat("function foo(x: Int): Int requires x > 0i; { return 1i; } public function main(a: Int): Int { return foo(a); }", "(assert (not (is-@Result-err (Main@main 0))))");
    });

    /*
    it("should exec simple postcond", function () {
        runMainCodeError("function foo(x: Int): Int requires x > 0i; { return 1i; } public function main(): Int { return foo(0i); }", "Error -- x > 0i @ test.bsq:3");
    });
    */
});

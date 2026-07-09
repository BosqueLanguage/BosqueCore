"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- NamespaceFunction Pre/Post", () => {
    it("should exec simple positional", function () {
        runTestSet("function foo(x: Int): Int requires x > 0i; { return 1i; } public function main(z: Int): Int { return foo(z); }", [['5i', '1i']], ['0i']);
        runTestSet("function foo(x: Int): Int ensures $return > 0i; { return 1i; } public function main(z: Int): Int { return foo(z); }", [['5i', '1i']], ['0i']);
    });
});

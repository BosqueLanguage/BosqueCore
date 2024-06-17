"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- simple declare only", () => {
    it("should type simple declares", function () {
        checkTestFunction("function main(): Int { var x: Int; return 0i; }");
        checkTestFunction("function main(): Bool { var x: Bool; return true; }");
    });
});

describe ("Checker -- simple declare-assign only", () => {
    it("should type simple declare-assign", function () {
        checkTestFunction("function main(): Int { var x: Int = 5i; return x; }");
        checkTestFunction("function main(): Bool { let x: Bool = true; return x; }");
    });

    it("should type simple declare-assign infer type", function () {
        checkTestFunction("function main(): Int { var x = 5i; return x; }");
        checkTestFunction("function main(): Bool { let x = true; return x; }");
    });

    it("should fail simple wrong result type", function () {
        checkTestFunctionError("function main(): Bool { let x = 5i; return x; }", "Expected a return value of type Bool but got Int");
    });
});

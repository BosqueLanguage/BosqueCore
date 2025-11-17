"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- NamespaceFunction Pre/Post", () => {
    it("should check simple positional", function () {
        checkTestFunction("function foo(x: Int): Int requires x > 0i; { return 1i; } function main(): Int { return foo(5i); }");
        checkTestFunction("function foo(x: Int): Int ensures $return > 0i; { return 1i; } function main(): Int { return foo(5i); }");
    });

    it("should check (fail) simple positional", function () {
        checkTestFunctionError("function foo(x: Int): Int requires x > 0n; { return 1i; } function main(): Int { return foo(5i); }", 'Operator > requires 2 arguments of the same type');
        checkTestFunctionError("function foo(x: Int): Int ensures $return > 0n; { return 1i; } function main(): Int { return foo(5i); }", 'Operator > requires 2 arguments of the same type');
    });
});

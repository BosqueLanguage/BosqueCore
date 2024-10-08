"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- switch Statement", () => {
    it("should check simple switch", function () {
        checkTestFunction("function main(): Int { let x = 3i; switch(x) { 0i => { return 0i; } | _ => { return 1i; } } }");
    });

    it("should check fail simple switch", function () {
        checkTestFunctionError("function main(): Int { let x = 3i; switch(x) { 0i => { return 0i; } } }", 'Switch statement must have 2 or more choices');
        checkTestFunctionError("function main(): Int { let x = 3i; switch(x) { _ => { return 1i; } | 0i => { return 0i; } } }", 'wildcard should be last option in switch expression but there were 1 more that are unreachable');
        checkTestFunctionError("function main(): Int { let x = 3i; switch(x) { 0n => { return 0i; } | _ => { return 1i; } } }", 'Cannot compare arguments in switch statement Nat');
    });

    it("should check enum switch", function () {
        checkTestFunction("enum Foo { f, g } function main(): Int { let x = Foo#f; switch(x) { Foo#f => { return 0i; } | _ => { return 1i; } } }");
        checkTestFunction("enum Foo { f, g } function main(): Int { let x = Foo#f; switch(x) { Foo#f => { return 0i; } | Foo#g => { return 1i; } } }");
    });
});

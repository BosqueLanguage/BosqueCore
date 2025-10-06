"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- match Statement", () => {
    it("should check simple match", function () {
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); match(x) { None => { return 0i; } | _ => { return 1i; } } }");
        checkTestFunction("datatype Foo of | F1 {} | F2 {}; function main(): Int { let x: Foo = F1{}; match(x) { F1 => { return 0i; } | F2 => { return 1i; } } }");
    });

    it("should check fail simple match", function () {
        checkTestFunctionError("function main(): Int { let x: Int = 3i; match(x) { Int => { return 0i; } | _ => { return 1i; } } }", 'Test is never false -- but there were 1 more that are unreachable');
        checkTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); match(x)@ { _ => { return 1i; } | None => { return 0i; } } }", 'wildcard should be last option in switch expression but there were 1 more that are unreachable');

        checkTestFunctionError("datatype Foo of | F1 {} | F2 { g: Int }; function main(): Int { let x: Foo = F1{}; match(x) { F1 => { return 0i; } | F2 => { return $x.g; } } }", 'Variable $x is not declared here');
    });

    it("should check binder match", function () {
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); match(x)@ { None => { return 0i; } | _ => { return 1i; } } }");
        checkTestFunction("datatype Foo of | F1 {} | F2 { g: Int }; function main(): Int { let x: Foo = F1{}; match(x)@ { F1 => { return 0i; } | F2 => { return $x.g; } } }");
    });

    it("should check binder match err", function () {
        checkTestFunctionError("datatype Foo of | F1 {} | F2 { g: Int }; function main(): Int { let x: Foo = F1{}; match(x)@ { F1 => { return $x.g; } | F2 => { return $x.g; } } }", 'Could not find field g in type F1');
    });
});

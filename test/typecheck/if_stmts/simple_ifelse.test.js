"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- IfElse Statement", () => {
    it("should check simple ifs", function () {
        checkTestFunction("function main(): Int { if(true) { return 3i; } else { return 1i; } }");

        checkTestFunctionError("function main(): Int { if(3i) { return 3i; } else { return 1i; } }", "If test requires a Bool type");
        checkTestFunctionError("function main(): Int { if(true) { return 3i; } else { return false; } }", "Expected a return value of type Int but got Bool");
    });

    it("should check itest ifs", function () {
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } else { return 1i; } }");

        checkTestFunctionError("function main(): Int { let x: Some<Int> = some(3i); if(x)some { return 3i; } else { return 1i; } }", "Test is never false -- false branch of if is unreachable");
    });

    it("should check binder itest ifs", function () {
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $x; } else { return 1i; } }");
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if($y = x)@some { return $y; } else { return 1i; } }");
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)@none { return 1i; } else { return $x; } }");

        checkTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 1i; } else { return $x; } }", "Variable $x is not declared here");
        checkTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $y; } else { return 1i; } }", "Variable $y is not declared here");
        checkTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return x; } else { return 1i; } }", "Expected a return value of type Int but got Option<Int>");
    });

    it("should check binder & reflow itest ifs", function () {
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)@@!some { return 0i; } else { ; } return x; }");

        checkTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if(x)@!some { return 0i; } else { ; } return x; }", "Expected a return value of type Int but got Option<Int>");
    });
});

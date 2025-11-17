"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- IfElse Statement", () => {
    it("should parse simple ifs", function () {
        parseTestFunction("function main(): Int { if(true) { return 3i; } else { return 1i; } }", undefined);

        parseTestFunctionError("function main(): Int { if(true) { return 3i; } else { } return 1i; }", "Empty block statement -- should include a ';' to indicate intentionally empty block");

        parseTestFunctionError("function main(): Int { if(true) return 3i; else { return 1i; } }", "Expected ITest");
        parseTestFunctionError("function main(): Int { if(true) { return 3i; } else return 1i; }", 'Expected "{" but got "return" when parsing "block statement"');
        parseTestFunctionError("function main(): Int { if true return 3i; else { return 1i; } }", 'Expected "(" but got "true" when parsing "if test"');
    });

    it("should parse itest ifs", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } else { return 1i; } }", undefined);
    });

    it("should parse binder itest ifs", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $x; } else { return 1i; } }", undefined);
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if($y = x)@some { return $y; } else { return 1i; } }", undefined);
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 1i; } else { return $x; } }", undefined);

        parseTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if(x)@some { $x = 0i; return $x; } else { return 1i; } }", "Invalid identifier name -- must start with a lowercase letter or _");
        parseTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if($y = x)some { return $y; } else { return 1i; } }", "Cannot have binder name without '@' or '@@'");
    });

    it("should parse binder & reflow itest ifs", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)@@!some { return 0i; } else { ; } return x; }", undefined);
    });
});

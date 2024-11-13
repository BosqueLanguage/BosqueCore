"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- If Statement", () => {
    it("should parse simple ifs", function () {
        parseTestFunction("function main(): Int { if(true) { return 3i; } return 1i; }", undefined);

        parseTestFunctionError("function main(): Int { if(true) { }; return 1i; }", "Empty block statement -- should include a ';' to indicate intentionally empty block");

        parseTestFunctionError("function main(): Int { if(true) return 3i; return 1i; }", "Expected ITest");
        parseTestFunctionError("function main(): Int { if true return 3i; return 1i; }", 'Expected "(" but got "true" when parsing "if test"');
    });

    it("should parse itest ifs", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)some { return 3i; } return 1i; }", undefined);
    });

    it("should parse binder itest ifs", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)@some { return $x; } return 1i; }", undefined);
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if($y = x)@some { return $y; } return 1i; }", undefined);

        parseTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if($y = x)some { return $y; } return 1i; }", "Cannot have binder name without '@' or '@@'");
    });

    it("should parse binder & reflow itest ifs", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if(x)@@!some { return 0i; } return x; }", undefined);

        parseTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if($y = x)@@some { return $y; } return 1i; }", "Cannot have postflow without implicitdef or using a non-variable expression");
    });
});

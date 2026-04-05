"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- If Statement", () => {
    it("should parse simple ifs", function () {
        parseTestFunction("function main(): Int { if (true) { return 3i; } return 1i; }", undefined);
        parseTestFunction("function main(): Int { if (true && true) { return 3i; } return 1i; }", undefined);

        parseTestFunctionError("function main(): Int { if (true &&) { return 3i; } return 1i; }", "Missing closing ')' in expression");

        parseTestFunctionError("function main(): Int { if (true) { }; return 1i; }", "Empty block statement -- should include a ';' to indicate intentionally empty block");

        parseTestFunctionError("function main(): Int { if (true) return 3i; return 1i; }", 'Expected "{" but got "return" when parsing "block statement"');
        parseTestFunctionError("function main(): Int { if true return 3i; return 1i; }", 'Expected "{" but got "return" when parsing "block statement"');
    });

    it("should parse ifs w/ single itest specials", function () {
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)!none { return 1i; } return 3i; }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)some { return 1i; } return 3i; }", undefined);
        
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)@!none { return $x; } return 3i; }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)@some { return $x; } return 3i; }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if ($z = x)@some { return $z; } return 3i; }", undefined);

        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if (x)@some { return $x; } return 1i; }", undefined);
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@some { return $y; } return 1i; }", undefined);
    });

    it("should parse ifs w/ single itest specials fails", function () {
        parseTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); if($y = x)some { return $y; } return 1i; }", 'Expected "@" but got "some" when parsing "binder in ITest guard"');
    });

    it("should parse ifs w/ single itest types", function () {
        parseTestFunction("function main(x: Option<Int>): Int { if (x)<Some> { return 1i; } return 3i; }", undefined);

        parseTestFunction("function main(x: Option<Int>): Some<Int> { if (x)@!<None> { return $x; } return some(3i); }", undefined);
        parseTestFunction("function main(x: Option<Int>): Some<Int> { if ($y = x)@<Some> { return $y; } return some(3i); }", undefined);

        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if (x)@some { return $x; } return 1i; }", undefined);
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@some { return $y; } return 1i; }", undefined);
    });

    it("should parse ifs w/ multi itest", function () {
    });

    it("should parse ifs w/ passing params", function () {
    });
});

"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- IfElse Statement", () => {
    it("should parse simple if-else statements", function () {
        parseTestFunction("function main(): Int { if (true) { return 3i; } else { return 1i; } }", undefined);
        parseTestFunction("function main(): Int { if (true || false) { return 3i; } else { return 1i; } }", undefined);

        parseTestFunctionError("function main(): Int { if (true || +) { return 3i; } else { return 1i; } }", "Unrecognized token");

        parseTestFunctionError("function main(): Int { if(true) { return 3i; } else { } return 1i; }", "Empty block statement -- should include a ';' to indicate intentionally empty block");

        parseTestFunctionError("function main(): Int { if(true) return 3i; else { return 1i; } }", 'Expected "{" but got "return" when parsing "block statement"');
        parseTestFunctionError("function main(): Int { if(true) { return 3i; } else return 1i; }", 'Expected "{" but got "return" when parsing "block statement"');
        parseTestFunctionError("function main(): Int { if true return 3i; else { return 1i; } }", 'Expected "(" but got "true" when parsing "if statement cond"');
    });

    it("should parse if-else w/ single itest specials", function () {
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)!none { return 1i; } else { return 3i; } }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)some { return 1i; } else { return 3i; } }", undefined);
        
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)@!none { return $x; } else { return 3i; } }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)@some { return $x; } else { return 3i; } }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if ($z = x)@some { return $z; } else { return 3i; } }", undefined);

        parseTestFunction("public function main(x: Option<Int>): Int { if (x)@none { return 3i; } else { return $x; } }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if (x)@!some { return 3i; } else { return $x; } }", undefined);
        parseTestFunction("public function main(x: Option<Int>): Int { if ($z = x)@!some { return 3i; } else { return $z; } }", undefined);

        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if (x)@some { return $x; } else { return 1i; } }", undefined);
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@some { return $y; } else { return 1i; } }", undefined);

        parseTestFunction("public function main(x: Option<Option<Int>>): Int { if (x.@some)@!some { return 3i; } else { return $_; } }", undefined);
    });

    it("should parse ifs w/ single itest types", function () {
        parseTestFunction("function main(x: Option<Int>): Int { if (x)<Some<Int>> { return 1i; } else { return 3i; } }", undefined);

        parseTestFunction("function main(x: Option<Int>): Some<Int> { if (x)@!<None> { return $x; } else { return some(3i); } }", undefined);
        parseTestFunction("function main(x: Option<Int>): Some<Int> { if ($y = x)@<Some<Int>> { return $y.value; } else { return some(3i); } }", undefined);

        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if (x)@<Some<Int>> { return $x.value; } else { return 1i; } }", undefined);
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@!<Some<Int>> { return 3i; } else { return $y.value; } }", undefined);
    });

    it.todo("should parse if-else w/ multi itest", function () {
    });

    it.todo("should parse if-else w/ passing params", function () {
    });
});

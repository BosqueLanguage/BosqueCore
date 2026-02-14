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
});

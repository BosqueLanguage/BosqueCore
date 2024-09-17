"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Abort", () => {
    it("should parse abort", function () {
        parseTestFunction("function main(): Int { abort; }", undefined);
    });
});

describe ("Parser -- Assert", () => {
    it("should parse asserts", function () {
        parseTestFunction("function main(): Int { assert(true); return 1i; }", "function main(): Int { assert true; return 1i; }");
        parseTestFunction("function main(): Int { assert true; return 1i; }", undefined);

        parseTestFunction("function main(): Int { assert test true; return 1i; }", undefined);
        parseTestFunction("function main(): Int { assert spec true; return 1i; }", undefined);
    });

    it("should fail parse asserts", function () {
        parseTestFunctionError("function main(): Int { assert; return 1i; }", "Unexpected token in expression -- ;");
        parseTestFunctionError("function main(): Int { assert(); return 1i; }", "Unexpected token in expression -- )");

        parseTestFunctionError("function main(): Int { assert tet true; return 1i; }", "Could not resolve 'tet' in this context");
    });
});

describe ("Parser -- Validate", () => {
    it("should parse validate", function () {
        parseTestFunction("function main(): Int { validate(true); return 1i; }", "function main(): Int { validate true; return 1i; }");
        parseTestFunction("function main(): Int { validate true; return 1i; }", undefined);
        parseTestFunction("function main(): Int { validate['Check#1'] true; return 1i; }", undefined);
    });

    it("should fail parse validate", function () {
        parseTestFunctionError("function main(): Int { validate(); return 1i; }", "Unexpected token in expression -- )");
        parseTestFunctionError("function main(): Int { validate[Check] true; return 1i; }", 'Expected "[LITERAL_EX_STRING]" but got "Check" when parsing "validate statement tag"');
    });
});


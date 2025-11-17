"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- multi declare-assign only", () => {
    it("should parse multi declare-assign", function () {
        parseTestFunction("function main(): Int { var x: Int, y: Bool = 1i, true; return x; }", undefined);
        parseTestFunction("function main(): Int { var x: Int, _: Bool = 1i, true; return x; }", undefined);
        
        parseTestFunction("function main(): Int { var x, y = 1i, true; return x; }", undefined);
        parseTestFunction("function main(): Int { var x, _ = 1i, true; return x; }", undefined);

        parseTestFunction("function main(): Int { var x, _, _ = 1i, true, false; return x; }", undefined);

        parseTestFunction("function main(): Int { var x: Int, _, z: Int = 1i, true, 0i; return x; }", undefined);
    });

    it("should parse multi declare-assign from elist", function () {
        parseTestFunction("function main(): Int { var x: Int, y: Bool = (|1i, true|); return x; }", undefined);
        parseTestFunction("function main(): Int { var x: Int, _: Bool = (|1i, true|); return x; }", undefined);
        
        parseTestFunction("function main(): Int { var x, y = (|1i, true|); return x; }", undefined);
        parseTestFunction("function main(): Int { var x, _ = (|1i, true|); return x; }", undefined);

        parseTestFunction("function main(): Int { var x, _, _ = (|1i, true, false|); return x; }", undefined);
    });

    it("should fail multi declare-assign only missing ,", function () {
        parseTestFunctionError("function main(): Int { var x: Int, y: Bool = 1i true; return x; }", "Mismatch in number of variables and expressions in assignment");
        parseTestFunctionError("function main(): Int { var x: Int y: Bool = 1i, true; return x; }", 'Expected a ";" or an assignment after variable declaration but got [IDENTIFIER]');
    });
});

describe ("Parser -- multi assign", () => {
    it("should parse multi assign", function () {
        parseTestFunction("function main(): Int { var x: Int = 1i; x, _ = 2i, false; return x; }", undefined);
    });
});


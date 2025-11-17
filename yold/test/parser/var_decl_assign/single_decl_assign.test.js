"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- simple declare only", () => {
    it("should parse simple declares", function () {
        parseTestFunction("function main(): Int { var x: Int; return 0i; }", undefined);
        parseTestFunction("function main(): Bool { var x: Bool; return true; }", undefined);
    });

    it("should fail declare only -- bad name $", function () {
        parseTestFunctionError("function main(x: Int): Int { var $y: Int; return 0i; }", "Invalid identifier name -- must start with a lowercase letter or _");
    });

    it("should fail declare only -- bad name _", function () {
        parseTestFunctionError("function main(x: Int): Int { var _: Int; return 0i; }", "Variable _ cannot be defined");
    });

    it("should fail declare only -- const var", function () {
        parseTestFunctionError("function main(x: Int): Int { let y: Int; return 0i; }", "Cannot declare as const without an assignment");
    });

    it("should fail declare only -- missing type", function () {
        parseTestFunctionError("function main(x: Int): Int { var y; return 0i; }", "Cannot declare a variable with an auto type without an assignment");
    });

    it("should fail declare only -- shadow", function () {
        parseTestFunctionError("function main(x: Int): Int { var x: Int; return 1i; }", "Variable x cannot be defined");
    });
});

describe ("Parser -- simple declare-assign only", () => {
    it("should parse simple declare-assign", function () {
        parseTestFunction("function main(): Int { var x: Int = 1i; return x; }", undefined);
        parseTestFunction("function main(): Bool { let x: Bool = true; return x; }", undefined);
        parseTestFunction("function main(): Bool { let x = true; return x; }", undefined);
    });

    it("should fail declare-assign only -- bad name $", function () {
        parseTestFunctionError("function main(x: Int): Int { var $y: Int = 1i; return 0i; }", "Invalid identifier name -- must start with a lowercase letter or _");
    });

    it("should fail declare-assign only -- shadow", function () {
        parseTestFunctionError("function main(x: Int): Int { let x: Int = 3i; return 1i; }", "Variable x cannot be defined");
    });

    it("should fail simple no decl naked _", function () {
        parseTestFunctionError("function main(): Bool { let _ = 5i; return x; }", "Variable _ cannot be defined");
    });
});

describe ("Parser -- simple assign", () => {
    it("should parse simple assign", function () {
        parseTestFunction("function main(): Int { var x: Int = 1i; x = 2i; return x; }", undefined);
        parseTestFunction("function main(): Int { _ = 2i; return 0i; }", undefined);
    });

    it("should fail assign -- const", function () {
        parseTestFunctionError("function main(): Int { let x = 1i; x = 2i; return x; }", "Cannot assign to variable x");
    });

    it("should fail assign -- const arg", function () {
        parseTestFunctionError("function main(x: Int): Int { x = 2i; return x; }", "Cannot assign to variable x");
    });

    it("should fail assign -- undecl", function () {
        parseTestFunctionError("function main(x: Int): Int { y = 2i; return 0i; }", "Cannot assign to variable y");
    });
});


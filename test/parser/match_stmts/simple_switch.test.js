"use strict";

import { parseTestFunction, parseTestFunctionError, parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- switch Statement", () => {
    it("should parse simple switch", function () {
        parseTestFunction("function main(): Int { let x = 3i; switch(x) { | 0i => { return 0i; } | _ => { return 1i; } } }", undefined);
    });

    it("should parse fail simple switch", function () {
        parseTestFunctionError("function main(): Int { let x = 3i; switch(x) { 0i => { return 0i; } | _ => { return 1i; } } }", 'Expected "|" but got "0i" when parsing "switch statement entry"');
        parseTestFunctionError("function main(): Int { let x = 3i; switch(x) { | 0i => return 0i; | _ => return 1i; } }", 'Expected "{" but got "return" when parsing "block statement"');
        parseTestFunctionError("function main(): Int { let x = 3i; switch(x) { | 0i => { return 0i; } _ => { return 1i; } } }", 'Expected "}" but got "_" when parsing "switch statement options"');
        parseTestFunctionError("function main(): Int { let x = 3i; switch(x) { | (1i + 2i) => { return 0i; } | _ => { return 1i; } } }", 'Expected literal expression');
    });

    it("should parse enum switch", function () {
        parseTestFunctionInFile("enum Foo { f, g } [FUNC]", "function main(): Int { let x = Foo#f; switch(x) { | Foo#f => { return 0i; } | _ => { return 1i; } } }");
        parseTestFunctionInFile("enum Foo { f, g } [FUNC]", "function main(): Int { let x = Foo#f; switch(x) { | Foo#f => { return 0i; } | Foo#g => { return 1i; } } }");
    });
});

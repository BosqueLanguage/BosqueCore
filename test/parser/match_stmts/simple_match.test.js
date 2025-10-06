"use strict";

import { parseTestFunction, parseTestFunctionError, parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- match Statement", () => {
    it("should parse simple match", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); match(x) { None => { return 0i; } | _ => { return 1i; } } }", undefined);
        parseTestFunctionInFile("datatype Foo of | F1 {} | F2 {}; [FUNC]", "function main(): Int { let x: Foo = F1{}; match(x) { F1 => { return 0i; } | F2 => { return 1i; } } }");
    });

    it("should parse fail simple match", function () {
        parseTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); match(x) { | None => { return 0i; } | _ => { return 1i; } } }", 'Expected " => " but got "|" when parsing "match statement entry"');
        parseTestFunctionError("datatype Foo of | F1 {} | F2 {}; function main(): Int { let x: Foo = F1{}; match(x) { F1 => return 0i; | F2 => return 1i; } }", 'Expected "{" but got "return" when parsing "block statement"');
        parseTestFunctionError("datatype Foo of | F1 {} | F2 {}; function main(): Int { let x: Foo = F1{}; match(x) { F1 => { return 0i; } F2 => { return 1i; } } }", 'Expected "}" but got "F2" when parsing "switch statment options"');
    });

    it("should parse binder match", function () {
        parseTestFunction("function main(): Int { let x: Option<Int> = some(3i); match(x)@ { None => { return 0i; } | _ => { return 1i; } } }", undefined);
        parseTestFunctionInFile("datatype Foo of | F1 {} | F2 {}; [FUNC]", "function main(): Int { let x: Foo = F1{}; match(x)@ { F1 => { return 0i; } | F2 => { return 1i; } } }");
    });

    it("should parse binder match err", function () {
        parseTestFunctionError("function main(): Int { let x: Option<Int> = some(3i); match(x)@@ { None => { return 0i; } | _ => { return 1i; } } }", 'Expected "{" but got "@@" when parsing "match statement options"');
    });
});

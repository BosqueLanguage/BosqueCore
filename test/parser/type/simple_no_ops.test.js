"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- type decl of bool", () => {
    it("should parse bool type decl", function () {
        parseTestFunctionInFile('type Flag = Bool; [FUNC]', 'function main(): Flag { return true<Flag>; }'); 
    });

});

describe ("Parser -- type decl of number", () => {
    it("should parse numeric type decls", function () {
        parseTestFunctionInFile('type NVal = Int; [FUNC]', 'function main(): NVal { return -2i<NVal>; }');
        parseTestFunctionInFile('type FVal = Float; [FUNC]', 'function main(): FVal { return 0.0f<FVal>; }');    
    });
});

describe ("Parser -- type decl of number with value", () => {
    it("should parse numeric type decls", function () {
        parseTestFunctionInFile('type NVal = Int; [FUNC]', 'function main(): Int { let x = -2i<NVal>; return x.value; }');    
    });
});

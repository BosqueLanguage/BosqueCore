"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- from operation", () => {
    it("should parse simple from Number", function () {
        parseTestFunctionInFile('type Foo = Int; [FUNC]', 'function main(): Foo { return Foo::from(3i); }'); 
        parseTestFunctionInFile('type Foo = Int; type Bar = Int; [FUNC]', 'function main(x: Bar): Foo { return Foo::from(x); }'); 

        parseTestFunctionInFile('type Foo = Int & { invariant $value > 0i; } [FUNC]', 'function main(): Foo { return Foo::from(3i); }'); 
    });

    it("should parse simple from String", function () {
        parseTestFunctionInFile('type Foo = CString; [FUNC]', "function main(): Foo { return Foo::from('ok'); }"); 
        parseTestFunctionInFile('type Foo = CString; type Bar = CString; [FUNC]', "function main(x: Bar): Foo { return Foo::from(x); }"); 

        parseTestFunctionInFile('type Foo = CString of /[a-z]+/; [FUNC]', "function main(): Foo { return Foo::from('ok'); }"); 
        parseTestFunctionInFile('type Foo = CString of /[0-9]{2}/; type Bar = CString; [FUNC]', "function main(x: Bar): Foo { return Foo::from(x); }"); 
    });
});

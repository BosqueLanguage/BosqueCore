"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- from operation", () => {
    it("should check simple from Number", function () {
        checkTestFunctionInFile('type Foo = Int; function main(): Foo { return Foo::from(3i); }'); 
        checkTestFunctionInFile('type Foo = Int; type Bar = Int; function main(x: Bar): Foo { return Foo::from(x); }'); 

        checkTestFunctionInFile('type Foo = Int & { invariant $value > 0i; } function main(): Foo { return Foo::from(3i); }'); 
    });

    it("should check simple from Number fails", function () {
        checkTestFunctionInFileError('type Foo = Int; function main(): Foo { return Foo::from(3n); }', 'Invalid arg type for conversion from Nat -- converting to Foo'); 
        checkTestFunctionInFileError('type Foo = Int; type Bar = Float; function main(x: Bar): Foo { return Foo::from(x); }', 'Invalid arg type for conversion from Bar -- converting to Foo'); 
    });

    it("should check simple from String", function () {
        checkTestFunctionInFile("type Foo = CString; function main(): Foo { return Foo::from('ok'); }"); 
        checkTestFunctionInFile("type Foo = CString; type Bar = CString; function main(x: Bar): Foo { return Foo::from(x); }"); 

        checkTestFunctionInFile("type Foo = CString of /[a-z]+/c; function main(): Foo { return Foo::from('ok'); }"); 
        checkTestFunctionInFile("type Foo = CString of /[0-9]{2}/c; type Bar = CString; function main(x: Bar): Foo { return Foo::from(x); }"); 
    });
});

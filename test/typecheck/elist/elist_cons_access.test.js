"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- elist decl and access", () => {
    it("should check simple elist", function () {
        checkTestFunction('function main(): Int { return (|2i, true|).0; }'); 
        checkTestFunction('function main(): Bool { return (|2i, true|).1; }'); 

        checkTestFunction('function main(): Bool { let x = (|2i, true|); return x.1; }'); 
    });

    it("should check option elist", function () {
        checkTestFunction('function main(): Int { let x: Option<(|Int, Bool|)> = some((|2i, true|)); return x@some.0; }'); 
    });

    it("should check fail simple elist", function () {
        checkTestFunctionError('function main(): Int { return (|2i, true|).3; }', 'Index 3 out of bounds for elist type (|Int, Bool|)');

        checkTestFunctionError('function main(): Int { return (|2i, true|).1; }', 'Expected a return value of type Int but got Bool');
    });
});


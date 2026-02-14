"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- IfElse Statement", () => {
    it("should check simple else ifs", function () {
        checkTestFunction("function main(): Int { if(true) { return 3i; } else { return 1i; } }");

        checkTestFunction("function main(b: Bool): Int { if (b) { abort; } else { return 1i; } }");
        checkTestFunction("function main(b: Bool): Int { if (b) { return 3i; } else { abort; } }");
        checkTestFunction("function main(b: Bool): Int { if (b) { abort; } else { assert 4i < 5i; } return 3i;}");

        checkTestFunctionError("function main(): Int { if(3i) { return 3i; } else { return 1i; } }", 'Guard expression does not evaluate to boolean');
        checkTestFunctionError("function main(): Int { if(true) { return 3i; } else { return false; } }", "Expected a return value of type Int but got Bool");
    });

    it("should check type alias ifelses", function () {
        checkTestFunctionInFile("type Foo = Bool; function main(): Int { if(true<Foo>) { return 3i; } else { return 1i; } }");
        checkTestFunctionInFileError("type Foo = Int; function main(): Int { if(3i<Foo>) { return 3i; } else { return 1i; } }", 'Guard expression does not evaluate to boolean');
    });
});


"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- access nested namespace functions", () => {
    it("should check top to nested", function () {
        checkTestFunctionInFile("namespace NSX { function foo(): Int { return 3i; } } function main(x: Int): Int { return NSX::foo(); }");
    });

    it("should check nested cross", function () {
        checkTestFunctionInFile("namespace NSX { function bar(): Int { return NSX::foo(); } function foo(): Int { return 3i; } } function main(x: Int): Int { return NSX::bar(); }");
        checkTestFunctionInFile("namespace NSX { function bar(): Int { return foo(); } function foo(): Int { return 3i; } } function main(x: Int): Int { return NSX::bar(); }");
    });

    it("should check nested up", function () {
        checkTestFunctionInFile("function foo(): Int { return 3i; } namespace NSX { function bar(): Int { return foo(); } } function main(x: Int): Int { return NSX::bar(); }");
        checkTestFunctionInFile("function foo(): Int { return 3i; } namespace NSX { function bar(): Int { return Main::foo(); } } function main(x: Int): Int { return NSX::bar(); }");
    });

    it("should check nested internal first", function () {
        checkTestFunctionInFile("function foo(): Int { return 3i; } namespace NSX { function foo(): Int { return 0i; } function bar(): Int { return foo(); } } function main(x: Int): Int { return NSX::bar(); }");
        checkTestFunctionInFile("function foo(): Nat { return 3n; } namespace NSX { function foo(): Int { return 3i; } function bar(): Int { return foo(); } } function main(x: Int): Int { return NSX::bar(); }");

        checkTestFunctionInFile("function foo(): Int { return 3i; } namespace NSX { function foo(): Nat { return 0n; } function bar(): Int { return Main::foo(); } } function main(x: Int): Int { return NSX::bar(); }");

        checkTestFunctionInFileError("function foo(): Int { return 3i; } namespace NSX { function foo(): Nat { return 0i; } function bar(): Int { return foo(); } } function main(x: Int): Int { return NSX::bar(); }", "Expected a return value of type Nat but got Int");
    });
});

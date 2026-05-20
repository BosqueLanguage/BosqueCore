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

    it("should check if-else w/ single itest specials", function () {
        checkTestFunction("public function main(x: Option<Int>): Int { if (x)!none { return 1i; } else { return 3i; } }");
        checkTestFunction("public function main(x: Option<Int>): Int { if (x)some { return 1i; } else { return 3i; } }");

        checkTestFunction("public function main(x: Option<Int>): Int { if (x)@none { return 3i; } else { return $x; } }");
        checkTestFunction("public function main(x: Option<Int>): Int { if (x)@some { return $x; } else { return 3i; } }");
        checkTestFunction("public function main(x: Option<Int>): Int { if ($z = x)@some { return $z; } else { return 3i; } }");

        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if (x)@some { return $x; } else { return 1i; } }");
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@!some { return 1i; } else { return $y; } }");
    
        checkTestFunction("public function main(x: Option<Option<Int>>): Int { if (x.@some)@some { return $_; } else { return 3i; } }");
    });

    it("should check if-else w/ single itest types", function () {
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)<Foo> { return 1i; } else { return 3i; } }");

        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)@<Foo> { return $x.f; } else { return 3i; } }");
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)@!<Foo> { return 1i; } else { return 3i; } }");
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if ($y = x)@<Foo> { return $y.f; } else { return 3i; } }");

        checkTestFunctionInFile("function main(): Int { let x: Option<Int> = some(3i); if (x)@<Some<Int>> { return $x.value; } else { return 1i; } }");
        checkTestFunctionInFile("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@<Some<Int>> { return $y.value; } else { return 1i; } }");
    });

    it.todo("should check if-else w/ multi itest", function () {
    });

    it.todo("should check if-else w/ passing params", function () {
    });

    it("should check simple if-elif-else", function () {
        checkTestFunction("function main(x: Int): Int { if(x == 0i) { return 0i; } elif(x > 0i) { return 1i; } else { return -1i; } }");

        checkTestFunctionError("function main(x: Int): Int { if(x == 0i) { return 0i; } elif(x) { return 1i; } else { return -1i; } }", 'Expected a boolean expression but got Int');
        checkTestFunctionError("function main(x: Int): Int { if(x == 0i) { return 0i; } elif(x > 0i) { return true; } else { return -1i; } }", "Expected a return value of type Int but got Bool");
    });
});

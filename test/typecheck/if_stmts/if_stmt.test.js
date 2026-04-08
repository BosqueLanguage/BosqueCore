"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- If Statement", () => {
    it("should check simple ifs", function () {
        checkTestFunction("function main(): Int { if(true) { return 3i; } return 1i; }");

        checkTestFunction("function main(b: Bool): Int { if (b) { abort; } return 1i; }");

        checkTestFunctionError("function main(): Int { if(3i) { return 3i; } return 1i; }", 'Guard expression does not evaluate to boolean');
        checkTestFunctionError("function main(): Int { if(true) { return true; } return 1i; }", "Expected a return value of type Int but got Bool");
    });

    it("should check type alias ifs", function () {
        checkTestFunctionInFile("type Foo = Bool; function main(): Int { if(true<Foo>) { return 3i; } return 1i; }");

        checkTestFunctionInFileError("type Foo = Int; function main(): Int { if(3i<Foo>) { return 3i; } return 1i; }", 'Guard expression does not evaluate to boolean');
    });

    it("should check ifs w/ single itest specials", function () {
        checkTestFunction("public function main(x: Option<Int>): Int { if (x)!none { return 1i; } return 3i; }");
        checkTestFunction("public function main(x: Option<Int>): Int { if (x)some { return 1i; } return 3i; }");

        checkTestFunction("public function main(x: Option<Int>): Int { if (x)@!none { return $x; } return 3i; }");
        checkTestFunction("public function main(x: Option<Int>): Int { if (x)@some { return $x; } return 3i; }");
        checkTestFunction("public function main(x: Option<Int>): Int { if ($z = x)@some { return $z; } return 3i; }");

        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if (x)@some { return $x; } return 1i; }");
        checkTestFunction("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@some { return $y; } return 1i; }");
    
        checkTestFunction("public function main(x: Option<Option<Int>>): Int { if (x.@some)@some { return $_; } return 3i; }");
    });

    it("should check ifs w/ single itest specials error", function () {
        checkTestFunctionError("public function main(x: Option<Int>): Int { if (x)@none { return $x; } return 3i; }", 'Expected a return value of type Int but got None');
        checkTestFunctionError("public function main(x: Some<Int>): Int { if (x)@some { return $x; } return 3i; }", 'Test is never false');
        checkTestFunctionError("public function main(x: Some<Int>): Int { if (x)@none { return $x; } return 3i; }", 'Test is never true');
        checkTestFunctionError("public function main(x: Option<Int>): Int { if ($z = x)@some { return $q; } return 3i; }", 'Variable $q is not declared here');
    });

    it("should check ifs w/ single itest types", function () {
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)<Foo> { return 1i; } return 3i; }");

        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)@<Foo> { return $x.f; } return 3i; }");
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)@!<Foo> { return 1i; } return 3i; }");
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if ($y = x)@<Foo> { return $y.f; } return 3i; }");

        checkTestFunctionInFile("function main(): Int { let x: Option<Int> = some(3i); if (x)@<Some<Int>> { return $x.value; } return 1i; }");
        checkTestFunctionInFile("function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@<Some<Int>> { return $y.value; } return 1i; }");
    });

    it("should check ifs w/ single itest types error", function () {
        checkTestFunctionInFileError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)<Foo> { return x.f; } return 3i; }", 'Could not find field f in type Bar');
        checkTestFunctionInFileError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Int { if (x)!<Foo> { return 2i; } return $x.f; }", 'Variable $x is not declared here');
    });

    it.todo("should check ifs w/ multi itest", function () {
    });

    it.todo("should check ifs w/ passing params", function () {
    });
});

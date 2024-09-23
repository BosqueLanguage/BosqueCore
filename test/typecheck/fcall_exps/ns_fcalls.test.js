"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- NamespaceFunction (no template)", () => {
    it("should check simple positional", function () {
        checkTestFunction("function foo(): Int { return 1i; } function main(): Int { return foo(); }");
        checkTestFunction("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(1i, true); }");
    });

    it("should check simple named", function () {
        checkTestFunction("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(x=1i, y=true); }");
        checkTestFunction("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(y=true, x=1i); }");
    });

    it("should check simple mixed", function () {
        checkTestFunction("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(x=1i, true); }");
        checkTestFunction("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(y=true, 1i); }");
    });

    it("should check simple default", function () {
        checkTestFunction("function foo(x: Int, y: Int = $x): Int { return x + y; } function main(): Int { return foo(1i, 2i); }");
        checkTestFunction("function foo(x: Int, y: Int = $x): Int { return x + y; } function main(): Int { return foo(1i); }");
    });

    it("should fail simple positional", function () {
        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(1i); }", "Required argument y not provided");
        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(1i, true, 'ok'); }", "Too many arguments provided to function");

        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(1i, 2i); }", "Argument y expected type Bool but got Int");
        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(true, true); }", "Argument x expected type Int but got Bool");
    });

    it("should fail simple nominal", function () {
        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(x=1i); }", "Required argument y not provided");
        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(y=true); }", "Required argument x not provided");
        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(x=1i, 'ok', y=true); }", "Too many arguments provided to function");

        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(y=1i, x=2i); }", "Argument y expected type Bool but got Int");
        checkTestFunctionError("function foo(x: Int, y: Bool): Int { return x; } function main(): Int { return foo(y=true, x=true); }", "Argument x expected type Int but got Bool");
    });
});

describe ("Checker -- NamespaceFunction (with template)", () => {
    it("should check simple positional", function () {
        checkTestFunction("function foo<T>(x: T): T { return x; } function main(): Int { return foo<Int>(3i); }");
    });

    it("should fail Nat->Int simple positional", function () {
        checkTestFunctionError("function foo<T>(x: T): T { return x; } function main(): Int { return foo<Nat>(2i); }", "Argument x expected type Nat but got Int");
    });

    it("should fail U not defined", function () {
        checkTestFunctionError("function foo<T>(x: T): U { return x; } function main(): Int { return foo<Int>(2i); }", "Template type U is not defined");
        checkTestFunctionError("function foo<T>(x: U): T { return x; } function main(): Int { return foo<Int>(2i); }", "Template type U is not defined");

        checkTestFunctionError("function foo<T>(x: U): U { return x; } function main(): Int { return foo<Int>(2i); }", "Template type U is not defined");
    });

    it("should fail missing terms", function () {
        checkTestFunctionError("function foo(x: T): T { return x; } function main(): Int { return foo<Int>(2i); }", "Template type T is not defined");
        checkTestFunctionError("function foo<T>(x: T): T { return x; } function main(): Int { return foo(2i); }", "Invoke foo expected 1 terms but got 0");
    });
});

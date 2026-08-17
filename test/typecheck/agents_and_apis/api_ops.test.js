"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";
/*
describe ("Checker -- API Declarations", () => {
    it("should check simple api decl", function () {
        checkTestFunction('abstract api foo(n: Nat): Int; function main(): Int { return 1i; }');
        checkTestFunction('abstract api foo(n: Nat): Int requires n != 0n; ensures $return > 0i; ; function main(): Int { return 1i; }');
    });

    it("should check simple api decl fail", function () {
        checkTestFunctionError('abstract api foo(n: Nat): Int requires n != 0i; ensures $return > 0i; ; function main(): Int { return 1i; }', 'Operator != requires 2 arguments of the same type');

        checkTestFunctionError('abstract api foo(...l: List<Nat>): Int; function main(): Int { return 1i; }', 'Agent/API parameters cannot have rest parameters');
        checkTestFunctionError('abstract api foo(n: Nat = 0n): Int; function main(): Int { return 1i; }', 'Agent/API parameters cannot have default values');
    });
});

describe ("Checker -- API Calls", () => {
    it("should check simple api call", function () {
        checkTestFunction('abstract api foo(n: Nat): Int; api main(): Int { return api foo(3n); }');
        checkTestFunction('abstract api foo(n: Nat): Int; api main(): Int { let ii = api Main::foo(env{}, 3n); return ii; }');
    });

    it("should check simple api call fail", function () {
        checkTestFunctionError('abstract api foo(n: Nat): Int; function main(): Int { return api foo(3n); }', 'Agent invocations must occour in environment aware code (agent/api/task) mode');

        checkTestFunctionError('abstract api foo(n: Nat): Int; api main(): Bool { return api foo(3n); }', 'Expected a return value of type Bool but got Int');
        checkTestFunctionError('abstract api foo(n: Nat): Int; api main(): Int { return api foo(3i); }', 'Argument type Int is not a subtype of expected parameter type Nat');
    });
});
*/
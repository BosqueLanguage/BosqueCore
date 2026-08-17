"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";
/*
describe ("Checker -- Agent Declarations", () => {
    it("should check simple agent decl", function () {
        checkTestFunction('abstract agent foo(n: Nat): Int; function main(): Int { return 1i; }');
        checkTestFunction('abstract agent foo(n: Nat): Int requires n != 0n; ensures $return > 0i; ; function main(): Int { return 1i; }');
    });

    it("should check simple agent decl fail", function () {
        checkTestFunctionError('abstract agent foo(n: Nat): Int requires n != 0i; ensures $return > 0i; ; function main(): Int { return 1i; }', 'Operator != requires 2 arguments of the same type');

        checkTestFunctionError('abstract agent foo(...l: List<Nat>): Int; function main(): Int { return 1i; }', 'Agent/API parameters cannot have rest parameters');
        checkTestFunctionError('abstract agent foo(n: Nat = 0n): Int; function main(): Int { return 1i; }', 'Agent/API parameters cannot have default values');
    });
});

describe ("Checker -- Agent Calls", () => {
    it("should check simple agent call", function () {
        checkTestFunction('abstract agent foo(n: Nat): Int; api main(): Int { return agent foo(3n); }');
        checkTestFunction('abstract agent foo(n: Nat): Int; api main(): Int { let ii = agent Main::foo(env{}, 3n); return ii; }');

        checkTestFunction('abstract agent foo(n: Nat); api main(): Int { return agent foo<Int>(3n); }');
    });

    it("should check simple agent call fail", function () {
        checkTestFunctionError('abstract agent foo(n: Nat): Int; function main(): Int { return agent foo(3n); }', 'Agent invocations must occour in environment aware code (agent/api/task) mode');

        checkTestFunctionError('abstract agent foo(n: Nat): Int; api main(): Int { return agent foo<Int>(3n); }', 'Agent does not allow result forming');
        checkTestFunctionError('abstract agent foo(n: Nat); api main(): Int { return agent foo(3n); }', 'Agent requires type to form result into');

        checkTestFunctionError('abstract agent foo(n: Nat): Int; api main(): Bool { return agent foo(3n); }', 'Expected a return value of type Bool but got Int');
        checkTestFunctionError('abstract agent foo(n: Nat): Int; api main(): Int { return agent foo(3i); }', 'Argument type Int is not a subtype of expected parameter type Nat');
    });
});
*/
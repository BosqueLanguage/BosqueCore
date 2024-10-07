"use strict";

import { checkTestExp, checkTestExpError, checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- basic strict equals", () => {
    it("should check strict equals operations", function () {
        checkTestExp("0n === 1n", "Bool");
        checkTestExp("0n !== 1n", "Bool");
        checkTestExp("'ok' !== 'yes'", "Bool");

        checkTestFunction("function main(): Bool { let x = 3i; let y = 4i; return x !== y; }");
    });

    it("should check fail strict equals operations", function () {
        checkTestExpError("0n === 5i", "Bool", "Types Nat and Int are not comparable");
        checkTestExpError("'ok' !== none", "Bool", "Types CString and None are not comparable");
        checkTestExpError("none === none", "Bool", "Types None and None are not comparable");
    });
});

describe ("Checker -- Option strict equals", () => {
    it("should check strict equals option operations", function () {
        checkTestFunction("function main(): Bool { let x: Option<Int> = some(3i); return x === none; }");
        checkTestFunction("function main(): Bool { let x: Option<Int> = some(3i); return x !== none; }");
        checkTestFunction("function main(): Bool { let x: Option<Int> = some(3i); return none === x; }");

        checkTestFunction("function main(): Bool { let x: Option<Int> = none; return x === 3i; }");
        checkTestFunction("function main(): Bool { let x: Option<Int> = none; return 3i === x; }");
    });

    it("should check fail strict equals option operations", function () {
        checkTestFunctionError("function main(): Bool { let x: Option<Int> = none; let y: Option<Int> = some(3i); return y === x; }", "Types Option<Int> and Option<Int> are not comparable");
    });
});

describe ("Checker -- type alias strict equals", () => {
    it("should check type alias strict equals operations", function () {
        checkTestFunction("type Foo = Int; function main(): Bool { return 1i<Foo> === 1i<Foo>; }");
        checkTestFunction("type Foo = Int; function main(): Bool { return 1i<Foo> !== 1i<Foo>; }");

        checkTestFunction("type Foo = Int; function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x === none; }");
        checkTestFunction("type Foo = Int; function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 0i<Foo>; }");
    });

    it("should check type alias fail strict equals operations", function () {
        checkTestFunctionError("type Foo = Int; function main(): Bool { return 1i<Foo> === 1i; }", "Types Foo and Int are not comparable");
    });
});

describe ("Checker -- enum strict equals", () => {
    it("should check enum strict equals operations", function () {
        checkTestFunction("enum Foo { f, g } function main(): Bool { return Foo#f === Foo#f; }");
        checkTestFunction("enum Foo { f, g } function main(): Bool { return Foo#f !== Foo#f; }");
    });

    it("should check enum fail strict equals operations", function () {
        checkTestFunctionError("enum Foo { f, g } function main(): Bool { return Foo#f !== 1i; }", "Types Foo and Int are not comparable");
    });
});

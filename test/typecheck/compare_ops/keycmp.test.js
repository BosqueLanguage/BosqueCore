"use strict";

import { checkTestExp, checkTestExpError, checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- basic KeyComparator equals/less", () => {
    it("should check KeyComparator operations", function () {
        checkTestExp("KeyComparator::equal<Nat>(0n, 1n)", "Bool");
        checkTestExp("KeyComparator::less<Nat>(0n, 1n)", "Bool");

        checkTestExp("KeyComparator::equal<CString>('', 'ok')", "Bool");
        checkTestExp("KeyComparator::less<CString>('', 'ok')", "Bool");
    });

    it("should check fail KeyComparator operations", function () {
        checkTestExpError("KeyComparator::equal<Int>(0n, 1n)", "Bool", "err1");
        checkTestExpError("KeyComparator::equal<Int>(0i, 1n)", "Bool", "err2");
        checkTestExpError("KeyComparator::equal<Nat>(0n, 1n)", "Int", "err3");
        
        checkTestExpError("KeyComparator::less<Int>(0n, 1n)", "Bool", "err4");
        checkTestExpError("KeyComparator::less<Int>(0i, 1n)", "Bool", "err5");
        checkTestExpError("KeyComparator::less<Nat>(0n, 1n)", "Int", "err6");
    });

    it("should check fail (bad K) KeyComparator operations", function () {
        checkTestExpError("KeyComparator::equal<Float>(0.0f, 1.0f)", "Bool", "err91");
        checkTestExpError("KeyComparator::equal<Some<Int>>(Some<Int>{0i}, Some<Int>{1i})", "Bool", "err92");
    });
});

describe ("Checker -- type alias KeyComparator equals/less", () => {
    it("should check KeyComparator operations", function () {
        checkTestFunction("type Foo = Int; function main(): Bool { return KeyComparator::equal<Foo>(0i<Foo>, 1i<Foo>); }");
    });

    it("should check fail KeyComparator operations", function () {
        checkTestFunctionError("type Foo = Int; function main(): Bool { return KeyComparator::equal<Foo>(0i<Foo>, 1i); }", "errX");
    });

    it("should check fail (bad K) KeyComparator operations", function () {
        checkTestFunctionError("type Foo = Float; function main(): Bool { return KeyComparator::equal<Foo>(0.0f<Foo>, 1.0f<Foo>); }", "errY");
    });
});

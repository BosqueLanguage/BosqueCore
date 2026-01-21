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
        checkTestExpError("KeyComparator::equal<Int>(0n, 1n)", "Bool", "Type Nat is not a (keytype) of Int");
        checkTestExpError("KeyComparator::equal<Int>(0i, 1n)", "Bool", "Type Nat is not a (keytype) of Int");
        checkTestExpError("KeyComparator::equal<Nat>(0n, 1n)", "Int", "Expected a return value of type Int but got Bool");
        
        checkTestExpError("KeyComparator::less<Int>(0n, 1n)", "Bool", "Type Nat is not a (keytype) of Int");
        checkTestExpError("KeyComparator::less<Int>(0i, 1n)", "Bool", "Type Nat is not a (keytype) of Int");
        checkTestExpError("KeyComparator::less<Nat>(0n, 1n)", "Int", "Expected a return value of type Int but got Bool");
    });

    it("should check fail (bad K) KeyComparator operations", function () {
        checkTestExpError("KeyComparator::equal<Float>(0.0f, 1.0f)", "Bool", "Type Float is not a (keytype) of Float");
        checkTestExpError("KeyComparator::equal<Some<Int>>(Some<Int>{0i}, Some<Int>{1i})", "Bool", "Type Some<Int> is not a (keytype) of Some<Int>");
    });
});

describe ("Checker -- type alias KeyComparator equals/less", () => {
    it("should check KeyComparator operations", function () {
        checkTestFunction("type Foo = Int; function main(): Bool { return KeyComparator::equal<Foo>(0i<Foo>, 1i<Foo>); }");
    });

    it("should check fail type alias KeyComparator operations", function () {
        checkTestFunctionError("type Foo = Int; function main(): Bool { return KeyComparator::equal<Foo>(0i<Foo>, 1i); }", "Type Int is not a (keytype) of Foo");
    });

    it("should check fail (bad K) KeyComparator operations", function () {
        checkTestFunctionError("type Foo = Float; function main(): Bool { return KeyComparator::equal<Foo>(0.0f<Foo>, 1.0f<Foo>); }", "Type Foo is not a (keytype) of Foo");
    });
});

describe ("Checker -- enum KeyComparator equals/less", () => {
    it("should check KeyComparator operations", function () {
        checkTestFunction("enum Foo { f, g } function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, Foo#g); }");
        checkTestFunction("enum Foo { f, g } function main(): Bool { return KeyComparator::less<Foo>(Foo#f, Foo#g); }");
    });

    it("should check fail enum KeyComparator operations", function () {
        checkTestFunctionError("enum Foo { f, g } function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, 1i); }", "Type Int is not a (keytype) of Foo");
    });
});

"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- type decl of bool", () => {
    it("should parse bool type decl", function () {
        parseTestFunctionInFile('type Flag = Bool; [FUNC]', 'function main(): Flag { return true<Flag>; }'); 
    });

});

describe ("Parser -- type decl of number", () => {
    it("should parse numeric type decls", function () {
        parseTestFunctionInFile('type NVal = Int; [FUNC]', 'function main(): NVal { return -2i<NVal>; }');
        parseTestFunctionInFile('type FVal = Float; [FUNC]', 'function main(): FVal { return 0.0f<FVal>; }');    
    });
});

describe ("Parser -- type decl of number with invariants", () => {
    it("should parse numeric type decls", function () {
        parseTestFunctionInFile('type NVal = Int & { invariant $value > 0i; invariant $value <= 100i; } [FUNC]', 'function main(): Int { let x = -2i<NVal>; return 5i; }');    
    });
});

describe ("Parser -- type decl with consts", () => {
    it("should parse entity with consts", function () {
        parseTestFunctionInFile('type Foo = Int & { const c: Int = 3i; } [FUNC]', 'function main(): Int { return Foo::c; }'); 
    });

    it("should parse entity with consts errors", function () {
        parseTestFunctionInFileError('type Foo = Int & { field c: Int; } function main(): Nat { return 4n; }', "Cannot have a field member on this type"); 
    });
});

describe ("Parser -- type decl with Int range bounds", () => {
    it("should parse Int with both bounds", function () {
        parseTestFunctionInFile('type Bounded = Int{-10i, 10i}; [FUNC]', 'function main(): Bounded { return 5i<Bounded>; }');
    });

    it("should parse Int with min only", function () {
        parseTestFunctionInFile('type Positive = Int{0i, }; [FUNC]', 'function main(): Positive { return 1i<Positive>; }');
    });

    it("should parse Int with max only", function () {
        parseTestFunctionInFile('type Capped = Int{, 100i}; [FUNC]', 'function main(): Capped { return 50i<Capped>; }');
    });

    it("should parse Int with negative lower bound", function () {
        parseTestFunctionInFile('type Fahrenheit = Int{-459i, }; [FUNC]', 'function main(): Fahrenheit { return 32i<Fahrenheit>; }');
    });
});

describe ("Parser -- type decl with Nat range bounds", () => {
    it("should parse Nat with both bounds", function () {
        parseTestFunctionInFile('type Percentage = Nat{0n, 100n}; [FUNC]', 'function main(): Percentage { return 50n<Percentage>; }');
    });

    it("should parse Nat with min only", function () {
        parseTestFunctionInFile('type AtLeastOne = Nat{1n, }; [FUNC]', 'function main(): AtLeastOne { return 5n<AtLeastOne>; }');
    });
});

describe ("Parser -- type decl with Float range bounds", () => {
    it("should parse Float with both bounds", function () {
        parseTestFunctionInFile('type Probability = Float{0.0f, 1.0f}; [FUNC]', 'function main(): Probability { return 0.5f<Probability>; }');
    });

    it("should parse Float with negative lower bound", function () {
        parseTestFunctionInFile('type NormFloat = Float{-1.0f, 1.0f}; [FUNC]', 'function main(): NormFloat { return 0.0f<NormFloat>; }');
    });
});

describe ("Parser -- type decl with Decimal range bounds", () => {
    it("should parse Decimal with both bounds", function () {
        parseTestFunctionInFile('type SmallDec = Decimal{-1.0d, 1.0d}; [FUNC]', 'function main(): SmallDec { return 0.5d<SmallDec>; }');
    });
});

describe ("Parser -- type decl numeric range with invariants", () => {
    it("should parse Int range combined with invariant body", function () {
        parseTestFunctionInFile('type EvenBounded = Int{0i, 100i} & { invariant $value == 0i; } [FUNC]', 'function main(): EvenBounded { return 0i<EvenBounded>; }');
    });
});

describe ("Parser -- type decl range bound type mismatch errors", () => {
    it("should reject Nat literals in Int range", function () {
        parseTestFunctionInFileError('type Bad = Int{0n, 100n}; function main(): Int { return 0i; }', "Range bound literal must match type Int");
    });

    it("should reject Int literals in Nat range", function () {
        parseTestFunctionInFileError('type Bad = Nat{0i, 100i}; function main(): Nat { return 0n; }', "Range bound literal must match type Nat");
    });

    it("should reject Nat literals in Float range", function () {
        parseTestFunctionInFileError('type Bad = Float{0n, 100n}; function main(): Float { return 0.0f; }', "Range bound literal must match type Float");
    });

    it("should reject Int literals in Decimal range", function () {
        parseTestFunctionInFileError('type Bad = Decimal{0i, 100i}; function main(): Decimal { return 0.0d; }', "Range bound literal must match type Decimal");
    });
});

describe ("Parser -- type decl string range still works", () => {
    it("should parse string size range with min only", function () {
        parseTestFunctionInFile('type UserName = String{5n, }; [FUNC]', 'function main(): UserName { return "hello"<UserName>; }');
    });

    it("should parse string size range with both bounds", function () {
        parseTestFunctionInFile('type ShortName = String{1n, 20n}; [FUNC]', 'function main(): ShortName { return "bob"<ShortName>; }');
    });
});
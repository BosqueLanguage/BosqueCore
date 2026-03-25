"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- type decl of bool", () => {
    it("should check bool type decl", function () {
        checkTestFunction('type Flag = Bool; function main(): Flag { return true<Flag>; }'); 
    });

    it("should fail not bool", function () {
        checkTestFunctionError("type Flag = Bool; function main(): Flag { return 3i<Flag>; }", "Literal value is not the same type (Int) as the value type (Bool)");
    });
});

describe ("Checker -- type decl of number", () => {
    it("should check numeric type decls", function () {
        checkTestFunction('type NVal = Int; function main(): NVal { return -2i<NVal>; }');
        checkTestFunction('type FVal = Float; function main(): FVal { return 0.0f<FVal>; }');    
    });

    it("should fail not int", function () {
        checkTestFunctionError("type NVal = Int; function main(): NVal { return 3n<NVal>; }", "Literal value is not the same type (Nat) as the value type (Int)");
    });
});

describe ("Checker -- type decl of number with invariants", () => {
    it("should check positional", function () {
        checkTestFunctionInFile('type Foo = Int & { invariant $value > 3i; } function main(): Foo { return Foo{1i}; }');
    });

    it("should fail missing names", function () {
        checkTestFunctionInFileError('type Foo = Int & { invariant $g > 3i; } function main(): Foo { return Foo{1i}; }', 'Variable $g is not declared here');
    });

    it("should fail bool", function () {
        checkTestFunctionInFileError('type Foo = Int & { invariant $value; } function main(): Foo { return Foo{3i}; }', 'Invariant expression does not have a boolean type -- got Int');
    });
});

describe ("Checker -- type decl of number with value", () => {
    it("should check numeric type decls", function () {
        checkTestFunction('type NVal = Int; function main(): NVal { let x = -2i<NVal>; return x; }');    
    });

    it("should fail not nat", function () {
        checkTestFunctionError('type II = Int; type NVal = II; function main(): Int { return 2i; }', "In type declaration value type must be simple primitive -- Bool, Int, etc.");
    });
});

describe ("Checker -- numeric range declaration validation", () => {
    it("should accept valid Int range", function () {
        checkTestFunction('type Foo = Int{1i, 10i}; function main(): Foo { return 5i<Foo>; }');
    });

    it("should accept valid Nat range", function () {
        checkTestFunction('type Foo = Nat{0n, 100n}; function main(): Foo { return 50n<Foo>; }');
    });

    it("should accept valid Float range", function () {
        checkTestFunction('type Foo = Float{0.0f, 1.0f}; function main(): Foo { return 0.5f<Foo>; }');
    });

    it("should accept valid Decimal range", function () {
        checkTestFunction('type Foo = Decimal{0.0d, 100.0d}; function main(): Foo { return 50.0d<Foo>; }');
    });

    it("should accept single-value exact range", function () {
        checkTestFunction('type Foo = Int{5i}; function main(): Foo { return 5i<Foo>; }');
    });

    it("should accept single-value exact Nat range", function () {
        checkTestFunction('type Foo = Nat{10n}; function main(): Foo { return 10n<Foo>; }');
    });

    it("should fail min > max", function () {
        checkTestFunctionError('type Foo = Int{10i, 5i}; function main(): Int { return 2i; }', "Range min (10i) must be <= max (5i)");
    });

    it("should fail min > max for Nat", function () {
        checkTestFunctionError('type Foo = Nat{100n, 10n}; function main(): Nat { return 2n; }', "Range min (100n) must be <= max (10n)");
    });

    it("should fail min > max for Float", function () {
        checkTestFunctionError('type Foo = Float{5.0f, 1.0f}; function main(): Float { return 1.0f; }', "Range min (5.0f) must be <= max (1.0f)");
    });
});

describe ("Checker -- numeric range value validation", () => {
    it("should accept value at min boundary", function () {
        checkTestFunction('type Foo = Int{5i, 10i}; function main(): Foo { return 5i<Foo>; }');
    });

    it("should accept value at max boundary", function () {
        checkTestFunction('type Foo = Int{5i, 10i}; function main(): Foo { return 10i<Foo>; }');
    });

    it("should fail value below min", function () {
        checkTestFunctionError('type Foo = Int{5i, 10i}; function main(): Foo { return 1i<Foo>; }', "Value 1i is below range minimum 5i");
    });

    it("should fail value above max", function () {
        checkTestFunctionError('type Foo = Int{5i, 10i}; function main(): Foo { return 20i<Foo>; }', "Value 20i is above range maximum 10i");
    });

    it("should fail value below exact single-bound", function () {
        checkTestFunctionError('type Foo = Int{5i}; function main(): Foo { return 4i<Foo>; }', "Value 4i is below range minimum 5i");
    });

    it("should fail value above exact single-bound", function () {
        checkTestFunctionError('type Foo = Int{5i}; function main(): Foo { return 6i<Foo>; }', "Value 6i is above range maximum 5i");
    });

    it("should fail Nat value below min", function () {
        checkTestFunctionError('type Foo = Nat{10n, 20n}; function main(): Foo { return 5n<Foo>; }', "Value 5n is below range minimum 10n");
    });

    it("should fail Nat value above max", function () {
        checkTestFunctionError('type Foo = Nat{10n, 20n}; function main(): Foo { return 25n<Foo>; }', "Value 25n is above range maximum 20n");
    });

    it("should fail Float value below min", function () {
        checkTestFunctionError('type Foo = Float{1.0f, 5.0f}; function main(): Foo { return 0.5f<Foo>; }', "Value 0.5f is below range minimum 1.0f");
    });

    it("should fail Float value above max", function () {
        checkTestFunctionError('type Foo = Float{1.0f, 5.0f}; function main(): Foo { return 10.0f<Foo>; }', "Value 10.0f is above range maximum 5.0f");
    });
});

describe ("Checker -- open-ended range validation", () => {
    it("should accept value above min-only bound", function () {
        checkTestFunction('type Foo = Int{5i, }; function main(): Foo { return 100i<Foo>; }');
    });

    it("should fail value below min-only bound", function () {
        checkTestFunctionError('type Foo = Int{5i, }; function main(): Foo { return 3i<Foo>; }', "Value 3i is below range minimum 5i");
    });

    it("should accept value below max-only bound", function () {
        checkTestFunction('type Foo = Int{, 10i}; function main(): Foo { return 5i<Foo>; }');
    });

    it("should fail value above max-only bound", function () {
        checkTestFunctionError('type Foo = Int{, 10i}; function main(): Foo { return 20i<Foo>; }', "Value 20i is above range maximum 10i");
    });
});

describe ("Checker -- negative literal value range validation", () => {
    it("should fail negative Int value below positive min", function () {
        checkTestFunctionError('type Foo = Int{1i, 10i}; function main(): Foo { return -3i<Foo>; }', "Value -3i is below range minimum 1i");
    });

    it("should fail negative Int value below exact single bound", function () {
        checkTestFunctionError('type Foo = Int{5i}; function main(): Foo { return -1i<Foo>; }', "Value -1i is below range minimum 5i");
    });
});

describe ("Checker -- ChkInt range validation", () => {
    it("should accept valid ChkInt range", function () {
        checkTestFunction('type Foo = ChkInt{1I, 10I}; function main(): Foo { return 5I<Foo>; }');
    });

    it("should fail min > max for ChkInt", function () {
        checkTestFunctionError('type Foo = ChkInt{10I, 5I}; function main(): ChkInt { return 2I; }', "Range min (10I) must be <= max (5I)");
    });

    it("should fail ChkInt value below min", function () {
        checkTestFunctionError('type Foo = ChkInt{5I, 10I}; function main(): Foo { return 3I<Foo>; }', "Value 3I is below range minimum 5I");
    });

    it("should fail ChkInt value above max", function () {
        checkTestFunctionError('type Foo = ChkInt{5I, 10I}; function main(): Foo { return 20I<Foo>; }', "Value 20I is above range maximum 10I");
    });
});

describe ("Checker -- ChkNat range validation", () => {
    it("should accept valid ChkNat range", function () {
        checkTestFunction('type Foo = ChkNat{10N, 20N}; function main(): Foo { return 15N<Foo>; }');
    });

    it("should fail min > max for ChkNat", function () {
        checkTestFunctionError('type Foo = ChkNat{100N, 10N}; function main(): ChkNat { return 2N; }', "Range min (100N) must be <= max (10N)");
    });

    it("should fail ChkNat value below min", function () {
        checkTestFunctionError('type Foo = ChkNat{10N, 20N}; function main(): Foo { return 5N<Foo>; }', "Value 5N is below range minimum 10N");
    });

    it("should fail ChkNat value above max", function () {
        checkTestFunctionError('type Foo = ChkNat{10N, 20N}; function main(): Foo { return 25N<Foo>; }', "Value 25N is above range maximum 20N");
    });
});

describe ("Checker -- Rational range validation", () => {
    it("should accept valid Rational range", function () {
        checkTestFunction('type Foo = Rational{1R, 5R}; function main(): Foo { return 3R<Foo>; }');
    });

    it("should fail min > max for Rational", function () {
        checkTestFunctionError('type Foo = Rational{5R, 1R}; function main(): Rational { return 1R; }', "Range min (5R) must be <= max (1R)");
    });

    it("should fail Rational value below min", function () {
        checkTestFunctionError('type Foo = Rational{2R, 5R}; function main(): Foo { return 1R<Foo>; }', "Value 1R is below range minimum 2R");
    });

    it("should fail Rational value above max", function () {
        checkTestFunctionError('type Foo = Rational{1R, 5R}; function main(): Foo { return 7R<Foo>; }', "Value 7R is above range maximum 5R");
    });
});

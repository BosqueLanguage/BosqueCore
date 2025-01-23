"use strict";

import { checkTestFunctionInFileError, runMainCode, runMainCodeError } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const decls = 'type Fahrenheit = Int; type Celsius = Int; type Percentage = Nat & { invariant $value <= 100n; } function isFreezing(temp: Celsius): Bool { return temp <= 0i<Celsius>; }'

describe ("type alias typechecks", () => {
    it("should typefail operations", function () {
        checkTestFunctionInFileError(`${decls} public function main(): Int { let x = 32i<Fahrenheit> + 0i<Celsius>; return 0i; }`, "Addition operator requires 2 arguments of the same type");
        checkTestFunctionInFileError(`${decls} public function main(): Bool { return isFreezing(5.0f); }`, "Argument temp expected type Celsius but got Float");
    });
});

describe ("type alias exec", () => {
    it("should succeed", function () {
        runMainCode(`${decls} public function main(): Nat { return 30n<Percentage>.value; }`, "30n"); 

        runMainCode(`${decls} public function main(): Bool { return isFreezing(5i<Celsius>); }`, "false");
        runMainCode(`${decls} public function main(): Bool { return isFreezing(-5i<Celsius>); }`, "true"); 
    });

    it("should fail", function () {
        runMainCodeError(`${decls} public function main(): Nat { return 101n<Percentage>.value; }`, 'Error -- failed invariant @ test.bsq'); 
    });
});

"use strict";

import { checkTestFunctionInFileError, runMainCode } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const decls = 'type Fahrenheit = Int; type Celsius = Int; type Percentage = Nat & { invariant $value <= 100n; } function isFreezing(temp: Celsius): Bool { return temp <= 0i<Celsius>; }'

describe ("type alias typechecks", () => {
    it("should typefail operations", function () {
        checkTestFunctionInFileError(`${decls} public function main(): Int { let x = 32i<Fahrenheit> + 0i<Celsius>; return 0i; }`, "err1");
        checkTestFunctionInFileError(`${decls} public function main(): Bool { return isFreezing(5.0f); }`, "err2");
    });
});

describe ("type alias exec", () => {
    it("should succeed", function () {
        runMainCode(`${decls} public function main(): Nat { return 30n<Percentage>.value; }`, [30n, "Nat"]); 

        runMainCode(`${decls} public function main(): Bool { return isFreezing(5i<Celsius>); }`, [false, "Bool"]);
        runMainCode(`${decls} public function main(): Bool { return isFreezing(-5i<Celsius>); }`, [true, "Bool"]); 
    });

    it("should fail", function () {
        runMainCode(`${decls} public function main(): Nat { return 101n<Percentage>.value; }`, [30n, "Nat"]); 
    });
});

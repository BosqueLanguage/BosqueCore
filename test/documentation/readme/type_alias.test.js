"use strict";

import { checkTestFunctionError, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const decls = 'type Fahrenheit = Int; type Celsius = Int; type Percentage = Nat & { invariant $value <= 100n; } function isFreezing(temp: Celsius): Bool { return temp <= 0i<Celsius>; }'

describe ("type alias typechecks", () => {
    it("should typefail operations", function () {
        checkTestFunctionError(`${decls} public function main(): Int { let x = 32i<Fahrenheit> + 0i<Celsius>; return 0i; }`, "Addition operator requires 2 arguments of the same type");
        checkTestFunctionError(`${decls} public function main(): Bool { return isFreezing(5.0f); }`, "Argument temp expected type Celsius but got Float");
    });
});

describe ("type alias exec", () => {
    it("should succeed", function () {
        runTestSet(`${decls} public function main(b: Bool): Nat { return 30n<Percentage>.value; }`, [['true', '30n']], []); 
        runTestSet(`${decls} public function main(t: Celsius): Bool { return isFreezing(t); }`, [['5i<Main::Celsius>', 'false'], ['-5i<Main::Celsius>', 'true']], []);

        runTestSet(`${decls} public function main(p: Percentage): Percentage { return 50n<Percentage> + p; }`, [['10n<Main::Percentage>', '60n<Main::Percentage>']], ['51n<Main::Percentage>']); 
    });
});

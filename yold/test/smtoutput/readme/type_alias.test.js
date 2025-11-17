"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

const decls = 'type Fahrenheit = Int; type Celsius = Int; type Percentage = Nat & { invariant $value <= 100n; } function isFreezing(temp: Celsius): Bool { return temp <= 0i<Celsius>; }'

describe ("SMT type alias exec", () => {
    it("SMT should succeed", function () {
        runishMainCodeUnsat(`${decls} public function main(): Nat { return 30n<Percentage>.value; }`, "(assert (not (= (@Result-ok 30) Main@main)))"); 

        runishMainCodeUnsat(`${decls} public function main(): Bool { return isFreezing(5i<Celsius>); }`, "(assert Main@main)");
        runishMainCodeUnsat(`${decls} public function main(): Bool { return isFreezing(-5i<Celsius>); }`, "(assert (not Main@main))"); 
    });

    it("SMT should fail", function () {
        runishMainCodeUnsat(`${decls} public function main(): Nat { return 101n<Percentage>.value; }`, "(assert (not (is-@Result-err Main@main)))"); 
    });
});

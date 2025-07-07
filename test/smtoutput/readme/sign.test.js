"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

const signf = 'function sign(x: Int): Int {var y: Int; if(x == 0i) { y = 0i; } else { y = if (x > 0i) then 1i else -1i; } return y; }';

describe ("SMT sign exec", () => {
    it("should exec sign", function () {
        runishMainCodeUnsat(`${signf} public function main(): Int { return sign(5i); }`, "(assert (not (= 1 Main@main)))"); 
        runishMainCodeUnsat(`${signf} public function main(): Int { return sign(-5i); }`, "(assert (not (= -1 Main@main)))");
        runishMainCodeUnsat(`${signf} public function main(): Int { return sign(0i); }`, "(assert (not (= 0 Main@main)))");
    });
});

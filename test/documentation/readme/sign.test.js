"use strict";

import { runMainCode } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const signf = 'function sign(x: Int): Int {var y: Int; if(x == 0i) { y = 0i; } else { y = if (x > 0i) then 1i else -1i; } return y; }';

describe ("sign exec", () => {
    it("should exec sign", function () {
        runMainCode(`${signf} public function main(): Int { return sign(5i); }`, "1i"); 
        runMainCode(`${signf} public function main(): Int { return sign(-5i); }`, "-1i");
        runMainCode(`${signf} public function main(): Int { return sign(0i); }`, "0i");
    });
});

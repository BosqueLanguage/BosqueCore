"use strict";

import { checkTestFunctionError, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

describe ("sign exec", () => {
    it("should exec sign", function () {
        runTestSet(`public function sign(x: Int): Int { if(x == 0i) { return 0i; } var y: Int; if(x < 0i) { y = -1i; } else { y = 1i; } return y; } public function main(x: Int): Int { return sign(x); }`, [["3i", "1i"], ["-5i", "-1i"], ["0i", "0i"]], []);
    });
});

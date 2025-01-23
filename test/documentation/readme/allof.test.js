"use strict";

import { runMainCode } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const allpositive = 'function allPositive(...args: List<Int>): Bool { return args.allOf(pred(x) => x >= 0i); }';

describe ("allof exec", () => {
    it("should exec allof", function () {
        runMainCode(`${allpositive} public function main(): Bool { return allPositive(1i, 3i, 4i); }`, "true"); 
        runMainCode(`${allpositive} public function main(): Bool { return allPositive(); }`, "true");
        runMainCode(`${allpositive} public function main(): Bool { return allPositive(1i, 3i, -4i); }`, "false");
    });
});

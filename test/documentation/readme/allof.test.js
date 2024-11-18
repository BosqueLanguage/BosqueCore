"use strict";

import { checkTestFunctionInFileError, runMainCode } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

describe ("allof exec", () => {
    it("should exec allof", function () {
        runMainCode('function allPositive(...args: List<Int>): Bool { return args.allOf(pred(x) => x >= 0i); } public function main(): Bool { return allPositive(1i, 3i, 4i); }', [true, "Bool"]); 
        runMainCode('function allPositive(...args: List<Int>): Bool { return args.allOf(pred(x) => x >= 0i); } public function main(): Bool { return allPositive(); }', [true, "Bool"]);
        runMainCode('function allPositive(...args: List<Int>): Bool { return args.allOf(pred(x) => x >= 0i); } public function main(): Bool { return allPositive(1i, 3i, -4i); }', [false, "Bool"]);
    });
});

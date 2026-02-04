"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Container Constructor (List)", () => {
    it("should emit simple list constructors", function () {
        checkTestEmitMainFunction("public function main(): List<Int> { return List<Int>{}; }", "xxxx");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{x}; }", "zzz");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{1i, x, 3i}; }", "yyyy");
    });

    it.skip("should emit spread and mixed list constructors", function () {
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l}; }", "aaa");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l, ...l}; }", "bbb");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }", "zzzz");
    });
});

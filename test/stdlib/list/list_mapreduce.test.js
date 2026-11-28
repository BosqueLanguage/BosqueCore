"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- mapreduce op", () => {
    it("should mapreduce list", function () {
        runTestSet(`public function main(z: Int): Bool { return List<Int>{}.mapreduce<Bool>(fn(v: Int) => v >= 1i, fn(acc: Bool, v: Bool) => acc & v, true); }`, [['1i', 'true']], []);  
        runTestSet(`public function main(z: Int): Bool { return List<Int>{1i, z, 3i}.mapreduce<Bool>(fn(v: Int) => v >= 1i, fn(acc: Bool, v: Bool) => acc & v, true); }`, [['1i', 'true'], ['0i', 'false']], []);  
    });
}); 

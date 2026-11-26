"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

const edecl = 'entity Foo { field f: Int; }';

describe ("List -- reduce op", () => {
    it("should reduce list", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.reduce(fn(b: Bool, y: Int) => b & y >= 1i, true); }', [['0i', 'true']], []);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.reduce(fn(b: Bool, y: Int) => b & y >= 0i, true); }', [['0i', 'false'], ['1i', 'true']], []); 
    });
});

describe ("List -- refduce op", () => {
    it("should refduce list", function () {
        runTestSet(`${edecl} public function main(z: Int): Foo { var ev = Foo{0i}; List<Int>{}.refduce<Foo>(fn(ref ev, y) => { ref ev[$f = $f + y]; }, ref ev); return ev; }`, [['0i', '0i']], []);  
        runTestSet(`${edecl} public function main(z: Int): Foo { return List<Int>{2i, z, 3i}.accumulate(fn(x: Int, y: Int) => x + y, 3i); }`, [['0i', '8i'], ['1i', '9i']], []); 
    });
});

describe ("List -- refreduce op", () => {
    it("should refreduce list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.accumulate(fn(x: Int, y: Int) => x + y, 0i); }', [['0i', '0i']], []);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.accumulate(fn(x: Int, y: Int) => x + y, 3i); }', [['0i', '8i'], ['1i', '9i']], []); 

        runTestSet(`${edecl} public function main(z: Int): Foo { return List<Foo>{Foo{3i}, Foo{2i}}.accumulate(fn(x, y) => Foo{x.f + y.f}, Foo{z}); }`, [['0i', 'Main::Foo{ 5i }'], ['1i', 'Main::Foo{ 6i }']], []);
    });
});
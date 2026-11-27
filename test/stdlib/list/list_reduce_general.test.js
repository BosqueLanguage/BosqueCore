"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

const edecl = 'entity Foo { field f: Int; }';

describe ("List -- reduce op", () => {
    it("should reduce list", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.reduce<Bool>(fn(b: Bool, y: Int) => b & y >= 1i, true); }', [['0i', 'true']], []);  
        runTestSet('public function main(z: Int): Bool { return List<Int>{2i, z, 3i}.reduce<Bool>(fn(b: Bool, y: Int) => b & y >= 0i, true); }', [['-1i', 'false'], ['1i', 'true']], []); 
    });
});

describe ("List -- refduce op", () => {
    it("should refduce list", function () {
        runTestSet(`${edecl} public function main(z: Int): Foo { var ev = Foo{0i}; List<Int>{}.refduce<Foo>(fn(ref ev, y) => { ref ev[f = $f + y]; }, ref ev); return ev; }`, [['0i', 'Main::Foo{ 0i }']], []);  
        runTestSet(`${edecl} public function main(z: Int): Foo { var ev = Foo{0i}; List<Int>{2i, z, 3i}.refduce<Foo>(fn(ref ev, y) => { ref ev[f = $f + y]; }, ref ev); return ev; }`, [['0i', 'Main::Foo{ 5i }'], ['1i', 'Main::Foo{ 6i }']], []); 
    });
});

describe ("List -- refreduce op", () => {
    it("should refreduce list", function () {
        runTestSet(`${edecl} public function main(z: Int): Int { var ev = Foo{0i}; let vv = List<Int>{}.refreduce<Foo, Int>(fn(ref ev, acc, y) => { ref ev[f = $f + y]; return acc + 2i; }, ref ev, 2i); return ev.f - vv; }`, [['0i', '-2i']], []);  
        runTestSet(`${edecl} public function main(z: Int): Int { var ev = Foo{0i}; let vv = List<Int>{2i, z, 3i}.refreduce<Foo, Int>(fn(ref ev, acc, y) => { ref ev[f = $f + y]; return acc + 2i; }, ref ev, 0i); return ev.f - vv; }`, [['0i', '-1i'], ['3i', '2i']], []); 
    });
});
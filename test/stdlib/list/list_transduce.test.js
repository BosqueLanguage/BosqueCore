"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

const edecl = 'entity Foo { field f: Int; }';

describe ("List -- transduce op", () => {
    it("should transduce list", function () {
        runTestSet(`${edecl} public function main(z: Int): List<Bool> { ref ev = Foo{0i}; return List<Int>{}.transduce<Foo, Bool>(fn(ref ev: Foo, y: Int): Bool => y >= 1i, ref ev); }`, [['0i', 'List<Bool>{ }']], []);  
        runTestSet(`${edecl} public function main(z: Int): List<Bool> { ref ev = Foo{0i}; return List<Int>{2i, z, 3i}.transduce<Foo, Bool>(fn(ref ev, y) => y >= 0i, ref ev); }`, [['-1i', 'List<Bool>{ true, false, true }'], ['1i', 'List<Bool>{ true, true, true }']], []); 

        runTestSet(`${edecl} public function main(z: Int): Bool { ref ev = Foo{0i}; let rr = List<Int>{2i, z, 3i}.transduce<Foo, Bool>(fn(ref ev, y) => { ref ev[f = $f + 1i]; return y >= 0i; }, ref ev); return rr.allOf(pred(b) => b) & ev.f == 3i; }`, [['-1i', 'false'], ['1i', 'true']], []); 
    });
});

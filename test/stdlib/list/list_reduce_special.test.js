"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

const edecl = 'entity Foo { field f: Int; }';

describe ("List -- sum numeric", () => {
    it("should sum list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.sum(); }', [['0i', '0i']], []);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.sum(); }', [['0i', '5i'], ['1i', '6i'], ['3i', '8i']], []); 
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, 1i, 3i, 1i, z}.sum(); }', [['0i', '7i'], ['1i', '8i'], ['3i', '10i']], []);         
    });
});

describe ("List -- accumulate op", () => {
    it("should accumulate list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.accumulate(fn(x: Int, y: Int) => x + y, 0i); }', [['0i', '0i']], []);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.accumulate(fn(x: Int, y: Int) => x + y, 3i); }', [['0i', '8i'], ['1i', '9i']], []); 

        runTestSet(`${edecl} public function main(z: Int): Foo { return List<Foo>{Foo{3i}, Foo{2i}}.accumulate(fn(x, y) => Foo{x.f + y.f}, Foo{z}); }`, [['0i', 'Main::Foo{ 5i }'], ['1i', 'Main::Foo{ 6i }']], []);
    });
});

describe ("List -- min keytype", () => {
    it("should min list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.min(); }', [], ['5i']);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.min(); }', [['0i', '0i'], ['5i', '2i'], ['3i', '2i']], []); 

        runTestSet("public function main(z: CString): CString { return List<CString>{'ok', z, 'k'}.min(); }", [['"xx"', "'k'"], ['"a"', "'a'"]], []);         
    });
});

describe ("List -- min cmp", () => {
    it("should min list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.min(pred(x: Int, y: Int) => x < y); }', [], ['5i']);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.min(pred(x: Int, y: Int) => x < y); }', [['0i', '0i'], ['5i', '2i'], ['3i', '2i']], []); 

        runTestSet(`${edecl} public function main(z: Int): Foo { return List<Foo>{Foo{3i}, Foo{z}, Foo{2i}}.min(pred(x, y) => x.f < y.f); }`, [['1i', 'Main::Foo{ 1i }'], ['5i', 'Main::Foo{ 2i }']], []);         
    });
});


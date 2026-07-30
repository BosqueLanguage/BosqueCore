"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

const edecl = 'entity Foo { field f: Int; }';
const epdecl = 'entity Foo { field f: Int; field g: Int; }';

describe ("List -- sum numeric", () => {
    it("should sum list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.sum(); }', [['0i', '0i']], []);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.sum(); }', [['0i', '5i'], ['1i', '6i'], ['3i', '8i']], ['4611686018427387900n']); 
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, 1i, 3i, 1i, z}.sum(); }', [['0i', '7i'], ['1i', '8i'], ['3i', '10i']], []);         
    });
});

describe ("List -- sum prefix numeric", () => {
    it("should sum list prefix", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.sumPrefix(); }', [['0i', 'List<Int>{ }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{2i, z, 3i}.sumPrefix(); }', [['0i', 'List<Int>{ 2i, 2i, 5i }'], ['1i', 'List<Int>{ 2i, 3i, 6i }'], ['3i', 'List<Int>{ 2i, 5i, 8i }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{2i, 1i, 3i, 1i, z}.sumPrefix(); }', [['0i', 'List<Int>{ 2i, 3i, 6i, 7i, 7i }'], ['1i', 'List<Int>{ 2i, 3i, 6i, 7i, 8i }'], ['3i', 'List<Int>{ 2i, 3i, 6i, 7i, 10i }']], []);
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
        runTestSet(`${epdecl} public function main(z: Int): Foo { return List<Foo>{Foo{3i, 1i}, Foo{z, 2i}, Foo{2i, 3i}}.min(pred(x, y) => x.f < y.f); }`, [['1i', 'Main::Foo{ 1i, 2i }'], ['5i', 'Main::Foo{ 2i, 3i }'], ['2i', 'Main::Foo{ 2i, 2i }']], []);
    });
});

describe ("List -- max keytype", () => {
    it("should max list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.max(); }', [], ['5i']);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.max(); }', [['0i', '3i'], ['5i', '5i'], ['3i', '3i']], []); 

        runTestSet("public function main(z: CString): CString { return List<CString>{'ok', z, 'k'}.max(); }", [['"xx"', "'xx'"], ['"a"', "'ok'"]], []);         
    });
});

describe ("List -- max cmp", () => {
    it("should max list", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.max(pred(x: Int, y: Int) => x < y); }', [], ['5i']);  
        runTestSet('public function main(z: Int): Int { return List<Int>{2i, z, 3i}.max(pred(x: Int, y: Int) => x < y); }', [['0i', '3i'], ['5i', '5i'], ['3i', '3i']], []); 

        runTestSet(`${edecl} public function main(z: Int): Foo { return List<Foo>{Foo{3i}, Foo{z}, Foo{2i}}.max(pred(x, y) => x.f < y.f); }`, [['1i', 'Main::Foo{ 3i }'], ['5i', 'Main::Foo{ 5i }']], []);
        runTestSet(`${epdecl} public function main(z: Int): Foo { return List<Foo>{Foo{1i, 1i}, Foo{z, 2i}, Foo{2i, 3i}}.max(pred(x, y) => x.f < y.f); }`, [['1i', 'Main::Foo{ 2i, 3i }'], ['5i', 'Main::Foo{ 5i, 2i }'], ['2i', 'Main::Foo{ 2i, 2i }']], []);
    });
});


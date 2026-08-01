"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

const datatypedef = 'datatype Foo of F1 { f: Int } F2 { g: Int };';

describe ("List -- map basic", () => {
    it("should do simple map", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.map<Int>(fn(x) => x + 2i); }', [['0i', 'List<Int>{ }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, z, 5i}.map<Int>(fn(x) => x + 2i); }', [['1i', 'List<Int>{ 3i, 3i, 7i }']], []);
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{1i, z, 5i}.map<Bool>(fn(x) => x >= 0i); }', [['1i', 'List<Bool>{ true, true, true }'], ['-1i', 'List<Bool>{ true, false, true }']], []);
    });
});

describe ("List -- map index basic", () => {
    it("should do simple map index", function () {
        runTestSet('public function main(z: Nat): List<Nat> { return List<Nat>{}.mapIdx<Nat>(fn(x, i) => x + i); }', [['0n', 'List<Nat>{ }']], []);
        runTestSet('public function main(z: Nat): List<Nat> { return List<Nat>{1n, z, 5n}.mapIdx<Nat>(fn(x, i) => x + i); }', [['1n', 'List<Nat>{ 1n, 2n, 7n }']], []);
        runTestSet('public function main(z: Nat): List<Bool> { return List<Nat>{1n, z, 5n}.mapIdx<Bool>(fn(x, i) => x > 0n && x != i); }', [['1n', 'List<Bool>{ true, false, true }'], ['0n', 'List<Bool>{ true, false, true }']], []);
    });
});


describe ("List -- convert", () => {
    it("should convert list", function () {
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{}.convert<F2>(); }`, [['true', 'List<Main::F2>{ }']], []);
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{ F2{5i} }.convert<F2>(); }`, [['true', 'List<Main::F2>{ Main::F2{ 5i } }']], []);
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{ F2{5i}, F2{5i}, F2{3i} }.convert<F2>(); }`, [['true', 'List<Main::F2>{ Main::F2{ 5i }, Main::F2{ 5i }, Main::F2{ 3i } }']], []);

        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{ F1{5i} }.convert<F2>(); }`, [], ['false']);
    });

    it("should convertsome list", function () {
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{}.convertsome<Int>(); }', [['true', 'List<Int>{ }']], []);  
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), some(1i)}.convertsome<Int>(); }', [['true', 'List<Int>{ 2i, 1i }']], []); 
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), some(1i), some(3i), some(1i), some(5i)}.convertsome<Int>(); }', [['true', 'List<Int>{ 2i, 1i, 3i, 1i, 5i }']], []);         

        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), none}.convertsome<Int>(); }', [], ['false']); 
    });
});

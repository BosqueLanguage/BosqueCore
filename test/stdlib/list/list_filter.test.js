"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

const datatypedef = 'datatype Foo of F1 { f: Int } F2 { g: Int };';

describe ("List -- filter", () => {
    it("should filter list", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.filter(pred(x: Int) => x <= z); }', [['0i', 'List<Int>{ }']], []);  
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{2i, 1i, 3i}.filter(pred(x: Int) => x <= z); }', [['0i', 'List<Int>{ }'], ['1i', 'List<Int>{ 1i }'], ['3i', 'List<Int>{ 2i, 1i, 3i }']], []); 
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{2i, 1i, 3i, 1i, 5i}.filter(pred(x: Int) => x <= z); }', [['0i', 'List<Int>{ }'], ['1i', 'List<Int>{ 1i, 1i }'], ['3i', 'List<Int>{ 2i, 1i, 3i, 1i }'], ['10i', 'List<Int>{ 2i, 1i, 3i, 1i, 5i }']], []);         
    });
});

describe ("List -- filtermap", () => {
    it("should filtermap list", function () {
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{}.filtermap<Bool>(pred(x: Int) => x <= z, fn(x: Int) => x == z); }', [['0i', 'List<Bool>{ }']], []);  
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{2i, 1i, 3i}.filtermap<Bool>(pred(x: Int) => x <= z, fn(x: Int) => x == z); }', [['0i', 'List<Bool>{ }'], ['1i', 'List<Bool>{ true }'], ['3i', 'List<Bool>{ false, false, true }']], []); 
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{2i, 1i, 3i, 1i, 5i}.filtermap<Bool>(pred(x: Int) => x <= z, fn(x: Int) => x == z); }', [['0i', 'List<Bool>{ }'], ['1i', 'List<Bool>{ true, true }'], ['3i', 'List<Bool>{ false, false, true, false }'], ['10i', 'List<Bool>{ false, false, false, false, false }']], []);         
    });
});

describe ("List -- convert(If)", () => {
    it("should convert list", function () {
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{}.convert<F2>(); }`, [['true', 'List<Main::F2>{ }']], []);
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{ F2{5i} }.convert<F2>(); }`, [['true', 'List<Main::F2>{ Main::F2{ 5i } }']], []);
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{ F2{5i}, F2{5i}, F2{3i} }.convert<F2>(); }`, [['true', 'List<Main::F2>{ Main::F2{ 5i }, Main::F2{ 5i }, Main::F2{ 3i } }']], []);

        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{ F1{5i} }.convert<F2>(); }`, [], ['false']);
    });

    it("should convertIf list", function () {
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{}.convertIf<F2>(); }`, [['true', 'List<Main::F2>{ }']], []);
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{F1{1i}, F2{5i}}.convertIf<F2>(); }`, [['true', 'List<Main::F2>{ Main::F2{ 5i } }']], []);
        runTestSet(`${datatypedef} public function main(b: Bool): List<F2> { return List<Foo>{ F1{1i}, F2{5i}, F1{2i}, F2{3i} }.convertIf<F2>(); }`, [['true', 'List<Main::F2>{ Main::F2{ 5i }, Main::F2{ 3i } }']], []);
    });
});

describe ("List -- extract(If)", () => {
    it("should extractSome list", function () {
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{}.extractSome<Int>(); }', [['true', 'List<Int>{ }']], []);  
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), some(1i)}.extractSome<Int>(); }', [['true', 'List<Int>{ 2i, 1i }']], []); 
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), some(1i), some(3i), some(1i), some(5i)}.extractSome<Int>(); }', [['true', 'List<Int>{ 2i, 1i, 3i, 1i, 5i }']], []);         

        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), none}.extractSome<Int>(); }', [], ['false']); 
    });

    it("should extractIfSome list", function () {
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{}.extractIfSome<Int>(); }', [['true', 'List<Int>{ }']], []);  
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), none}.extractIfSome<Int>(); }', [['true', 'List<Int>{ 2i }']], []); 
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), some(1i), none, some(1i), none}.extractIfSome<Int>(); }', [['true', 'List<Int>{ 2i, 1i, 1i }']], []); 
        runTestSet('public function main(b: Bool): List<Int> { return List<Option<Int>>{some(2i), some(1i), some(3i), some(1i), some(5i)}.extractIfSome<Int>(); }', [['true', 'List<Int>{ 2i, 1i, 3i, 1i, 5i }']], []);         
    });
});

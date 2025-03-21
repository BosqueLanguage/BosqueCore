"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- find basic", () => {
    it("should do simple find", function () {
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i, 1i}.find(pred(x) => x >= 2i); }', "2i");
        
        runMainCodeError('public function main(): Int { return List<Int>{1i, 2i, 3i}.find(pred(x) => x >= 4i)?none; }', "fail1");
    });
});

describe ("List -- findLast basic", () => {
    it("should do simple findLast", function () {
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i, 1i}.findLast(pred(x) => x >= 2i); }', "3i");
        
        runMainCodeError('public function main(): Int { return List<Int>{1i, 2i, 3i}.findLast(pred(x) => x >= 4i); }', "fail2");
    });
});

describe ("List -- tryFind basic", () => {
    it("should do simple tryFind", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.tryFind(pred(x) => x >= 0i)?none; }', "true");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i, 1i}.tryFind(pred(x) => x >= 2i)@some; }', "2i");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.tryFind(pred(x) => x >= 4i)?none; }', "true");
    });
});

describe ("List -- tryFindLast basic", () => {
    it("should do simple tryFindLast", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.tryFindLast(pred(x) => x >= 0i)?none; }', "true");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i, 1i}.tryFindLast(pred(x) => x >= 2i)@some; }', "3i");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.tryFindLast(pred(x) => x >= 4i)?none; }', "true");
    });
});

describe ("List -- contains basic", () => {
    it("should do simple contains", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.contains(0i); }', "false");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i, 1i}.contains(2i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.contains(4i); }', "false");
    });
});

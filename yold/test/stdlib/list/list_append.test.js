"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- append/concat", () => {
    it("should append", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.append(List<Int>{}).empty(); }', "true");

        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.append(List<Int>{}).size(); }', "2n");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.append(List<Int>{}).back(); }', "2i");
        runMainCode('public function main(): Nat { return List<Int>{}.append(List<Int>{1i, 2i}).size(); }', "2n"); 
        runMainCode('public function main(): Int { return List<Int>{}.append(List<Int>{1i, 2i}).front(); }', "1i");

        runMainCode('public function main(): Nat { return List<Int>{1i}.append(List<Int>{3i, 2i}).size(); }', "3n"); 
        runMainCode('public function main(): Int { return List<Int>{1i}.append(List<Int>{3i, 2i}).back(); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>{1i}.append(List<Int>{3i, 2i}).front(); }', "1i"); 
    });

    it("should prepend", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.prepend(List<Int>{}).empty(); }', "true");

        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.prepend(List<Int>{}).size(); }', "2n");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.prepend(List<Int>{}).back(); }', "2i");
        runMainCode('public function main(): Nat { return List<Int>{}.prepend(List<Int>{1i, 2i}).size(); }', "2n"); 
        runMainCode('public function main(): Int { return List<Int>{}.prepend(List<Int>{1i, 2i}).front(); }', "1i");

        runMainCode('public function main(): Nat { return List<Int>{1i}.prepend(List<Int>{3i, 2i}).size(); }', "3n"); 
        runMainCode('public function main(): Int { return List<Int>{1i}.prepend(List<Int>{3i, 2i}).back(); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i}.prepend(List<Int>{3i, 2i}).front(); }', "3i"); 
    });

    it("should concat", function () {
        runMainCode('public function main(): Bool { return List<Int>::concat().empty(); }', "true");

        runMainCode('public function main(): Nat { return List<Int>::concat(List<Int>{1i, 2i}, List<Int>{}).size(); }', "2n");
        runMainCode('public function main(): Int { return List<Int>::concat(List<Int>{1i, 2i}, List<Int>{}).back(); }', "2i");
        runMainCode('public function main(): Nat { return List<Int>::concat(List<Int>{}, List<Int>{1i, 2i}).size(); }', "2n"); 
        runMainCode('public function main(): Int { return List<Int>::concat(List<Int>{}, List<Int>{1i, 2i}).front(); }', "1i");

        runMainCode('public function main(): Nat { return List<Int>::concat(List<Int>{1i}, List<Int>{3i, 2i}).size(); }', "3n"); 
        runMainCode('public function main(): Int { return List<Int>::concat(List<Int>{1i}, List<Int>{3i, 2i}).back(); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>::concat(List<Int>{1i}, List<Int>{3i, 2i}).front(); }', "1i"); 
    });

    it("should concatAll", function () {
        runMainCode('public function main(): Bool { return List<Int>::concatAll(List<List<Int>>{}).empty(); }', "true");

        runMainCode('public function main(): Nat { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i, 2i}, List<Int>{}}).size(); }', "2n");
        runMainCode('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i, 2i}, List<Int>{}}).back(); }', "2i");
        runMainCode('public function main(): Nat { return List<Int>::concatAll(List<List<Int>>{List<Int>{}, List<Int>{1i, 2i}}).size(); }', "2n"); 
        runMainCode('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{}, List<Int>{1i, 2i}}).front(); }', "1i");

        runMainCode('public function main(): Nat { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i}, List<Int>{3i, 2i}}).size(); }', "3n"); 
        runMainCode('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i}, List<Int>{3i, 2i}}).back(); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i}, List<Int>{3i, 2i}}).front(); }', "1i");  
    });
});

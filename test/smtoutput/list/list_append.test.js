"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT List -- append/concat", () => {
    it("should append smt", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.append(List<Int>{}).empty(); }', "(assert (not (= (@Result-ok true) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.append(List<Int>{}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.append(List<Int>{}).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{}.append(List<Int>{1i, 2i}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.append(List<Int>{1i, 2i}).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i}.append(List<Int>{3i, 2i}).size(); }', "(assert (not (= (@Result-ok 3) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.append(List<Int>{3i, 2i}).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.append(List<Int>{3i, 2i}).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
    });

    it("should prepend smt", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.prepend(List<Int>{}).empty(); }', "(assert (not (= (@Result-ok true) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.prepend(List<Int>{}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.prepend(List<Int>{}).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{}.prepend(List<Int>{1i, 2i}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.prepend(List<Int>{1i, 2i}).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i}.prepend(List<Int>{3i, 2i}).size(); }', "(assert (not (= (@Result-ok 3) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.prepend(List<Int>{3i, 2i}).back(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.prepend(List<Int>{3i, 2i}).front(); }', "(assert (not (= (@Result-ok 3) Main@main)))"); 
    });

    it("should concat smt", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>::concat().empty(); }', "(assert (not (= (@Result-ok true) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>::concat(List<Int>{1i, 2i}, List<Int>{}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concat(List<Int>{1i, 2i}, List<Int>{}).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Nat { return List<Int>::concat(List<Int>{}, List<Int>{1i, 2i}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concat(List<Int>{}, List<Int>{1i, 2i}).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>::concat(List<Int>{1i}, List<Int>{3i, 2i}).size(); }', "(assert (not (= (@Result-ok 3) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concat(List<Int>{1i}, List<Int>{3i, 2i}).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concat(List<Int>{1i}, List<Int>{3i, 2i}).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
    });

    it("should concatAll smt", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>::concatAll(List<List<Int>>{}).empty(); }', "(assert (not (= (@Result-ok true) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i, 2i}, List<Int>{}}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i, 2i}, List<Int>{}}).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))");
        runishMainCodeUnsat('public function main(): Nat { return List<Int>::concatAll(List<List<Int>>{List<Int>{}, List<Int>{1i, 2i}}).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{}, List<Int>{1i, 2i}}).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))");

        runishMainCodeUnsat('public function main(): Nat { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i}, List<Int>{3i, 2i}}).size(); }', "(assert (not (= (@Result-ok 3) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i}, List<Int>{3i, 2i}}).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>::concatAll(List<List<Int>>{List<Int>{1i}, List<Int>{3i, 2i}}).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))");  
    });
});
"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Container Constructor (List)", () => {
    it("should exec simple list constructors", function () {
        runTestSet("public function main(x: Int): List<Int> { return List<Int>{}; }", [['5i', 'List<Int>{ }']], []);
        runTestSet("public function main(x: Int): List<Int> { return List<Int>{x}; }", [['5i', 'List<Int>{ 5i }'], ['0i', 'List<Int>{ 0i }']], []);
        runTestSet("public function main(x: Int): List<Int> { return List<Int>{1i, x, 3i}; }", [['5i', 'List<Int>{ 1i, 5i, 3i }'], ['0i', 'List<Int>{ 1i, 0i, 3i }']], []);
    
        runTestSet("public function main(y: CString): List<CString> { let s = 'ok'; return List<CString>{y, s}; }", [['"y"', "List<CString>{ 'y', 'ok' }"]], []);
        runTestSet("public function main(y: CString): List<CString> { let s = 'ok'; return List<CString>{y, s, 'a'}; }", [['"y"', "List<CString>{ 'y', 'ok', 'a' }"]], []);
    });

    it.skip("should exec spread and mixed list constructors", function () {
        runTestSet("public function main(l: List<Int>): List<Int> { return List<Int>{...l}; }", [], []);
        runTestSet("public function main(l: List<Int>): List<Int> { return List<Int>{...l, ...l}; }", [], []);
        runTestSet("public function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }", [], []);
    });

    it("should exec simple map constructors", function () {
        runTestSet("public function main(x: Int): Map<Int, Nat> { return Map<Int, Nat>{}; }", [['5i', 'Map<Int, Nat>{ }']], []);
        runTestSet("public function main(x: Int): Map<Int, Nat> { return Map<Int, Nat>{x => 2n}; }", [['5i', 'Map<Int, Nat>{ 5i => 2n }'], ['0i', 'Map<Int, Nat>{ 0i => 2n }']], []);
        runTestSet("public function main(x: MapEntry<Int, Nat>): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n, x}; }", [['MapEntry<Int, Nat>{5i, 5n}', 'Map<Int, Nat>{ 1i => 2n, 5i => 5n }'], ['MapEntry<Int, Nat>{0i, 0n}', 'Map<Int, Nat>{ 0i => 0n, 1i => 2n }']], ['MapEntry<Int, Nat>{1i, 100n}']);
    
        runTestSet("public function main(y: CString): Map<CString, Nat> { let s = 'ok'; return Map<CString, Nat>{y => 1n, s => 2n}; }", [['"y"', "Map<CString, Nat>{ 'y' => 1n, 'ok' => 2n }"]], []);
        runTestSet("public function main(y: CString): Map<CString, Nat> { let s = 'ok'; return Map<CString, Nat>{y => 1n, s => 2n, 'a' => 3n}; }", [['"y"', "Map<CString, Nat>{ 'a' => 3n, 'y' => 1n, 'ok' => 2n }"]], []);
    });

    it.skip("should exec spread and mixed map constructors", function () {
    });
});

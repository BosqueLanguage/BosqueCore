"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Map union", () => {
    it("should union", function () {
        runMainCode('public function main(): Bool { return Map<Int, CString>::union().empty(); }', "true");

        runMainCode("public function main(): Nat { return Map<Int, CString>::union(Map<Int, CString>{1i => 'a', 2i => 'b'}, Map<Int, CString>{}).size(); }", "2n");
        runMainCode("public function main(): CString { return Map<Int, CString>::union(Map<Int, CString>{1i => 'a', 2i => 'b'}, Map<Int, CString>{}).get(2i); }", "'b'");
        runMainCode("public function main(): Nat { return Map<Int, CString>::union(Map<Int, CString>{}, Map<Int, CString>{1i => 'a', 2i => 'b'}).size(); }", "2n"); 
        runMainCode("public function main(): CString { return Map<Int, CString>::union(Map<Int, CString>{}, Map<Int, CString>{1i => 'a', 2i => 'b'}).get(1i); }", "'a'");

        runMainCode("public function main(): Nat { return Map<Int, CString>::union(Map<Int, CString>{1i => 'a'}, Map<Int, CString>{3i => 'c', 2i => 'b'}).size(); }", "3n"); 
        runMainCode("public function main(): CString { return Map<Int, CString>::union(Map<Int, CString>{1i => 'a'}, Map<Int, CString>{3i => 'c', 2i => 'b'}).get(2i); }", "'b'"); 
        runMainCode("public function main(): CString { return Map<Int, CString>::union(Map<Int, CString>{1i => 'a'}, Map<Int, CString>{3i => 'c', 2i => 'b'}).get(1i); }", "'a'"); 
    });

    it("should unionAll", function () {
        runMainCode('public function main(): Bool { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{}).empty(); }', "true");

        runMainCode("public function main(): Nat { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{1i => 'a', 2i => 'b'}, Map<Int, CString>{}}).size(); }", "2n");
        runMainCode("public function main(): CString { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{1i => 'a', 2i => 'b'}, Map<Int, CString>{}}).get(2i); }", "'b'");
        runMainCode("public function main(): Nat { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{}, Map<Int, CString>{1i => 'a', 2i => 'b'}}).size(); }", "2n"); 
        runMainCode("public function main(): CString { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{}, Map<Int, CString>{1i => 'a', 2i => 'b'}}).get(1i); }", "'a'");

        runMainCode("public function main(): Nat { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{1i => 'a'}, Map<Int, CString>{3i => 'c', 2i => 'b'}}).size(); }", "3n"); 
        runMainCode("public function main(): CString { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{1i => 'a'}, Map<Int, CString>{3i => 'c', 2i => 'b'}}).get(2i); }", "'b'"); 
        runMainCode("public function main(): CString { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{1i => 'a'}, Map<Int, CString>{3i => 'c', 2i => 'b'}}).get(1i); }", "'a'"); 
    });

    it("should union fail (duplicates)", function () {
        runMainCodeError("public function main(): Nat { return Map<Int, CString>::union(Map<Int, CString>{1i => 'a'}, Map<Int, CString>{2i => 'a'}, Map<Int, CString>{1i => 'c'}).size(); }", "Error -- !KeyComparator::equal<K>(k, $t.v.key) @ xcore_map_exec.bsq");

        runMainCodeError("public function main(): Nat { return Map<Int, CString>::unionAll(List<Map<Int, CString>>{Map<Int, CString>{1i => 'a'}, Map<Int, CString>{2i => 'a'}, Map<Int, CString>{1i => 'c'}}).size(); }", "Error -- !KeyComparator::equal<K>(k, $t.v.key) @ xcore_map_exec.bsq");
    });
});

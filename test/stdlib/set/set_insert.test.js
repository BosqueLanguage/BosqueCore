"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe ("Set -- add/set/insert", () => {
    it("should insert", function () {
        runTestSet('public function main(z: Int): Set<Int> { return Set<Int>{}.insert(z); }', [['1i', 'Set<Int>{ 1i }']], []); 
        runTestSet('public function main(z: Int): Set<Int> { return Set<Int>{1i}.insert(z); }', [['2i', 'Set<Int>{ 1i, 2i }'], ['0i', 'Set<Int>{ 0i, 1i }'], ['1i', 'Set<Int>{ 1i }']], []);
    });

    it("should add", function () {
        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{}.add(i); }', [['0i', 'Set<Int>{ 0i }']], []);
        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{1i, 2i}.add(i); }', [['0i', 'Set<Int>{ 0i, 1i, 2i }'], ['11i', 'Set<Int>{ 1i, 2i, 11i }']], ['2i']); 
        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{1i, 2i, 3i}.add(i); }', [['0i', 'Set<Int>{ 0i, 1i, 2i, 3i }'], ['5i', 'Set<Int>{ 1i, 2i, 3i, 5i }']], ['3i']); 
    });

    it("should mixed ops", function () {
        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{1i, 2i}.add(3i).add(4i).insert(i); }', [['2i', 'Set<Int>{ 1i, 2i, 3i, 4i }'], ['11i', 'Set<Int>{ 1i, 2i, 3i, 4i, 11i }']], []);
        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{1i, 2i}.insert(i).add(4i).insert(2i).insert(i + 1i); }', [['2i', 'Set<Int>{ 1i, 2i, 3i, 4i }']], ['0i']);

        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{1i, 18i, 2i}.insert(i).insert(i + 1i).add(3i).add(4i); }', [['0i', 'Set<Int>{ 0i, 1i, 2i, 3i, 4i, 18i }'], ['5i', 'Set<Int>{ 1i, 2i, 3i, 4i, 5i, 6i, 18i }']], ['2i']);
    });

    it("should mixed ops w ref", function () {
        runTestSet('public function main(i: Int): Set<Int> { var m = Set<Int>{1i, 2i}; ref m.add(3i); ref m.add(4i); ref m.insert(i); return m; }', [['2i', 'Set<Int>{ 1i, 2i, 3i, 4i }'], ['11i', 'Set<Int>{ 1i, 2i, 3i, 4i, 11i }']], []);
        runTestSet('public function main(i: Int): Set<Int> { var m = Set<Int>{1i, 2i}; ref m.insert(i); ref m.add(4i); ref m.insert(2i); ref m.insert(i + 1i); return m; }', [['2i', 'Set<Int>{ 1i, 2i, 3i, 4i }']], ['0i']);
    });
});

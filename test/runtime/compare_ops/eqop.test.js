"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- basic strict equals", () => {
    it("should exec strict equals operations", function () {
        runMainCode("public function main(): Bool { return 0n === 1n; }", [false, "Bool"]);
        runMainCode("public function main(): Bool { return 0n !== 1n; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return 'ok' !== 'yes'; }", [true, "Bool"]);

        runMainCode("public function main(): Bool { let x = 3i; let y = 4i; return x !== y; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { let x = 3i; let y = 4i; return x === y; }", [false, "Bool"]);
    });
});

describe ("Exec -- Option strict equals", () => {
    it("should exec strict equals option operations", function () {
        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return x === none; }", [false, "Bool"]);
        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return x !== none; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return none === x; }", [false, "Bool"]);

        runMainCode("public function main(): Bool { let x: Option<Int> = none; return x === none; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { let x: Option<Int> = none; return x !== none; }", [false, "Bool"]);
        runMainCode("public function main(): Bool { let x: Option<Int> = none; return none === x; }", [true, "Bool"]);

        runMainCode("public function main(): Bool { let x: Option<Int> = none; return x === 3i; }", [false, "Bool"]);
        runMainCode("public function main(): Bool { let x: Option<Int> = none; return 3i === x; }", [false, "Bool"]);

        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return x === 3i; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { let x: Option<Int> = some(4i); return 3i === x; }", [false, "Bool"]);
    });
});

describe ("Exec -- type alias strict equals", () => {
    it("should exec type alias strict equals operations", function () {
        runMainCode("type Foo = Int; public function main(): Bool { return 1i<Foo> === 1i<Foo>; }", [true, "Bool"]);
        runMainCode("type Foo = Int; public function main(): Bool { return 1i<Foo> !== 1i<Foo>; }", [false, "Bool"]);

        runMainCode("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x === none; }", [false, "Bool"]);
        runMainCode("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 0i<Foo>; }", [true, "Bool"]);
        runMainCode("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 3i<Foo>; }", [false, "Bool"]);
    });
});
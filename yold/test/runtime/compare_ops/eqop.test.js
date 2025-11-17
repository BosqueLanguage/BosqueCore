"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- basic strict equals", () => {
    it("should exec strict equals operations", function () {
        runMainCode("public function main(): Bool { return 0n === 1n; }", "false");
        runMainCode("public function main(): Bool { return 0n !== 1n; }", "true");
        runMainCode("public function main(): Bool { return 'ok' !== 'yes'; }", "true");

        runMainCode("public function main(): Bool { let x = 3i; let y = 4i; return x !== y; }", "true");
        runMainCode("public function main(): Bool { let x = 3i; let y = 4i; return x === y; }", "false");
    });
});

describe ("Exec -- Option strict equals", () => {
    it("should exec strict equals option operations", function () {
        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return x === none; }", "false");
        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return x !== none; }", "true");
        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return none === x; }", "false");

        runMainCode("public function main(): Bool { let x: Option<Int> = none; return x === none; }", "true");
        runMainCode("public function main(): Bool { let x: Option<Int> = none; return x !== none; }", "false");
        runMainCode("public function main(): Bool { let x: Option<Int> = none; return none === x; }", "true");

        runMainCode("public function main(): Bool { let x: Option<Int> = none; return x === 3i; }", "false");
        runMainCode("public function main(): Bool { let x: Option<Int> = none; return 3i === x; }", "false");

        runMainCode("public function main(): Bool { let x: Option<Int> = some(3i); return x === 3i; }", "true");
        runMainCode("public function main(): Bool { let x: Option<Int> = some(4i); return 3i === x; }", "false");
    });
});

describe ("Exec -- type alias strict equals", () => {
    it("should exec type alias strict equals operations", function () {
        runMainCode("type Foo = Int; public function main(): Bool { return 1i<Foo> === 1i<Foo>; }", "true");
        runMainCode("type Foo = Int; public function main(): Bool { return 1i<Foo> !== 1i<Foo>; }", "false");

        runMainCode("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x === none; }", "false");
        runMainCode("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 0i<Foo>; }", "true");
        runMainCode("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 3i<Foo>; }", "false");
    });
});

"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- sum integrals", () => {
    it("should do simple integral sums", function () {
        runMainCode('public function main(): Int { return List<Int>{}.sum(); }', [0n, "Int"]);
        runMainCode('public function main(): Int { return List<Int>{2i, -1i}.sum(); }', [1n, "Int"]);

        runMainCode('public function main(): Nat { return List<Nat>{}.sum(); }', [0n, "Nat"]);
        runMainCode('public function main(): Nat { return List<Nat>{2n, 1n}.sum(); }', [3n, "Nat"]);
    });
});

describe ("List -- sum float", () => {
    it("should do simple float sums", function () {
        runMainCode('public function main(): Float { return List<Float>{}.sum(); }', [0.0, "Float"]);
        runMainCode('public function main(): Float { return List<Float>{2.0f, -1.0f}.sum(); }', [1.0, "Float"]);
    });
});

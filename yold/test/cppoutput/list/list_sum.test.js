"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate List -- sum integrals", () => {
    it("should do simple integral sums", function () {
        runMainCode('public function main(): Int { return List<Int>{}.sum(); }', "0_i");
        runMainCode('public function main(): Int { return List<Int>{2i, -1i}.sum(); }', "1_i");

        runMainCode('public function main(): Nat { return List<Nat>{}.sum(); }', "0_n");
        runMainCode('public function main(): Nat { return List<Nat>{2n, 1n}.sum(); }', "3_n");
    });
});

describe ("CPP Emit Evaluate List -- sum float", () => {
    it("should do simple float sums", function () {
        runMainCode('public function main(): Bool { let tmp = List<Float>{}.sum(); return (tmp < 0.1f && tmp > -0.1f);}', "true");
        runMainCode('public function main(): Bool { let tmp = List<Float>{2.0f, -1.0f}.sum(); return (tmp > 0.9f && tmp < 1.1f);}', "true");
    });
});

"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- access nested namespace functions", () => {
    it("should exec top to nested", function () {
        runMainCode("namespace NSX { function foo(): Int { return 3i; } } public function main(x: Int): Int { return NSX::foo(); }", "3i");
    });

    it("should exec nested cross", function () {
        runMainCode("namespace NSX { function bar(): Int { return NSX::foo(); } function foo(): Int { return 3i; } } public function main(x: Int): Int { return NSX::bar(); }", "3i");
        runMainCode("namespace NSX { function bar(): Int { return foo(); } function foo(): Int { return 3i; } } public function main(x: Int): Int { return NSX::bar(); }", "3i");
    });

    it("should exec nested up", function () {
        runMainCode("function foo(): Int { return 3i; } namespace NSX { function bar(): Int { return foo(); } } public function main(x: Int): Int { return NSX::bar(); }", "3i");
        runMainCode("function foo(): Int { return 3i; } namespace NSX { function bar(): Int { return Main::foo(); } } public function main(x: Int): Int { return NSX::bar(); }", "3i");
    });

    it("should exec nested internal first", function () {
        runMainCode("function foo(): Int { return 3i; } namespace NSX { function foo(): Int { return 0i; } function bar(): Int { return foo(); } } public function main(x: Int): Int { return NSX::bar(); }", "0i");
        runMainCode("function foo(): Nat { return 3n; } namespace NSX { function foo(): Int { return 3i; } function bar(): Int { return foo(); } } public function main(x: Int): Int { return NSX::bar(); }", "3i");

        runMainCode("function foo(): Int { return 3i; } namespace NSX { function foo(): Int { return 0i; } function bar(): Int { return foo(); } } public function main(x: Int): Int { return NSX::bar(); }", "0i");
        runMainCode("function foo(): Int { return 3i; } namespace NSX { function foo(): Nat { return 0n; } function bar(): Int { return Main::foo(); } } public function main(x: Int): Int { return NSX::bar(); }", "3i");
    });
});

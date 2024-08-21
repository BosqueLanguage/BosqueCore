"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple if-expression", () => {
    it("should exec simple", function () {
        runMainCode("public function main(): Int { return if(1n != 2n) then 2i else 3i; }", [2n, "Int"]);
        runMainCode("public function main(): Int { return if(2n != 2n) then 2i else 3i; }", [3n, "Int"]);
    });

    /*
    it("should exec expressions w/ itest", function () {
        runMainCode("public function main(): Int { x: Int? = ; return if(x)!none then 2i else 3i; }");
        runMainCode("public function main(x: Int?): Int { return if(x)some then 2i else 3i; }");
        runMainCode("public function main(x: Int?): Int { return if(x)<Some<Int>> then 2i else 3i; }");

        runMainCode("public function main(x: Int?): Int { return if(x)@!none then $x else 3i; }");
        runMainCode("public function main(x: Int): Int? { return if(x < 3i) then none else some(x); }");
        runMainCode("public function main(x: Int): Int { return if(if(x < 3i) then none else some(x))@!none then $_ else 3i; }");
        runMainCode("public function main(x: Int?): Int? { return if($y = x)@<Some<Int>> then $y else some(3i); }");
    });
    */
});

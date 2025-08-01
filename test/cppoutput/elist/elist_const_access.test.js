"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- elist decl and access", () => {
    it("should exec simple elist", function () {
        runMainCode('public function main(): Int { return (|2i, true|).0; }', "2_i"); 
        runMainCode('public function main(): Bool { return (|2i, true|).1; }', "true"); 

        runMainCode('public function main(): Bool { let x = (|2i, true|); return x.1; }', "true"); 
    });

/* TODO: This is a funny special case for Option<elist> and Some<elist> as we dont emit tinfo for elists themselves
    it("should exec option elist", function () {
        runMainCode('public function main(): Int { let x: Option<(|Int, Bool|)> = some((|2i, true|)); return x@some.0; }', "2i"); 
    });
*/
});
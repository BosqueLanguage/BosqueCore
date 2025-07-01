"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- elist decl and access", () => {
    it("should smt exec simple elist", function () {
        runishMainCodeUnsat('public function main(): Int { return (|2i, true|).0; }', "(assert (not (= 2 Main@main)))"); 
        runishMainCodeUnsat('public function main(): Bool { return (|2i, true|).1; }', "(assert (not Main@main))"); 

        runishMainCodeUnsat('public function main(): Bool { let x = (|2i, true|); return x.1; }', "(assert (not Main@main))"); 
    });

    it("should smt exec option elist", function () {
        runishMainCodeUnsat('public function main(): Int { let x: Option<(|Int, Bool|)> = some((|2i, true|)); return x@some.0; }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
    });
});

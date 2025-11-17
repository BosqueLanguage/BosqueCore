"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

const zipcode = 'type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/;';
const csspt = 'type CSSPt = String of /[0-9]+"pt"/; function is3pt(s1: CSSPt): Bool { return s1.value === "3pt"; }';

describe ("SMT -- type decl zipcode/css", () => {
    it("should smt exec string options type decl", function () {
        runishMainCodeUnsat(`${zipcode} public function main(): String { return "98052-0000"<Zipcode>.value; }`, '(assert (not (= "98052-0000" Main@main)))');

        runishMainCodeUnsat(`${csspt} public function main(): Bool { return is3pt("3pt"<CSSPt>); }`, '(assert (not Main@main))');
        runishMainCodeUnsat(`${csspt} public function main(): Bool { return is3pt("4pt"<CSSPt>); }`, '(assert Main@main)');
    });
});


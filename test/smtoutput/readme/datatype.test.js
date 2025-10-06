"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

const dtype = 'datatype BoolOp of | Const { val: Bool } | NotOp { arg: BoolOp } | AndOp { larg: BoolOp, rarg: BoolOp } | OrOp { larg: BoolOp, rarg: BoolOp } & { recursive method evaluate(): Bool { match(this)@ { Const  => { return $this.val; } | NotOp => { return !$this.arg.evaluate[recursive](); } | AndOp => { return $this.larg.evaluate[recursive]() && $this.rarg.evaluate[recursive](); } | OrOp  => { return $this.larg.evaluate[recursive]() || $this.rarg.evaluate[recursive](); } } } }';

describe ("SMT datatype exec", () => {
    it("SMT datatype should succeed", function () {
        runishMainCodeUnsat(`${dtype} public function main(): Bool { return OrOp{Const{true}, Const{false}}.evaluate[recursive](); }`, "(assert (not (= (@Result-ok true) Main@main)))");
        runishMainCodeUnsat(`${dtype} public function main(): Bool { return AndOp{larg=Const{true}, rarg=Const{false}}.evaluate[recursive](); }`, "(assert (not (= (@Result-ok false) Main@main)))");
    });
});



"use strict";

import { runMainCode } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const dtype = 'datatype BoolOp of Const { val: Bool } | NotOp { arg: BoolOp } | AndOp { larg: BoolOp, rarg: BoolOp } | OrOp { larg: BoolOp, rarg: BoolOp } & { recursive method evaluate(): Bool { match(this)@ { Const  => { return $this.val; } | NotOp => { return !$this.arg.evaluate[recursive](); } | AndOp => { return $this.larg.evaluate[recursive]() && $this.rarg.evaluate[recursive](); } | OrOp  => { return $this.larg.evaluate[recursive]() || $this.rarg.evaluate[recursive](); } } } }';

describe ("datatype exec", () => {
    it("datatype should succeed", function () {
        runMainCode(`${dtype} public function main(): Nat { return OrOp{Const{true}, Const{false}}.evaluate[recursive](); }`, [true, "Bool"]);
        runMainCode(`${dtype} public function main(): Nat { return AndOp{larg=Const{true}, rarg=Const{false}}.evaluate[recursive](); }`, [false, "Bool"]); 
    });
});


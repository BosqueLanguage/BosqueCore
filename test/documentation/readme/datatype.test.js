"use strict";

import { runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const dtype = 'datatype BoolOp of Const { val: Bool } NotOp { arg: BoolOp } AndOp { larg: BoolOp, rarg: BoolOp } OrOp { larg: BoolOp, rarg: BoolOp } & { recursive method evaluate(): Bool { match(this) { Const => { return $this.val; } NotOp => { return !$this.arg.evaluate[recursive](); } AndOp => { return $this.larg.evaluate[recursive]() && $this.rarg.evaluate[recursive](); } OrOp  => { return $this.larg.evaluate[recursive]() || $this.rarg.evaluate[recursive](); } } } }';

describe ("datatype exec", () => {
    it("datatype should succeed", function () {
        runTestSet(`${dtype} public function main(b: Bool): Bool { return OrOp{Const{b}, Const{false}}.evaluate[recursive](); }`, [['true', 'true'], ['false', 'false']], []);
        runTestSet(`${dtype} public function main(b: Bool): Bool { return AndOp{larg=Const{true}, rarg=Const{b}}.evaluate[recursive](); }`, [['true', 'true'], ['false', 'false']], []);
        runTestSet(`${dtype} public function main(b: Bool): Bool { return AndOp{larg=Const{true}, rarg=NotOp{arg=Const{b}}}.evaluate[recursive](); }`, [['true', 'false'], ['false', 'true']], []);
    });
});

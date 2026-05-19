"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- match Statement", () => {
    it("should emit simple match", function () {
        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); match(x) { None => { return 0i; } _ => { return 1i; } } }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; switch(x.typeinfo->bsqtypeid) { case 0 /** None **/: { None ᑯx = none; return 0_i; } default: { SomeᐸIntᐳ ᑯx = x.asSome(); return 1_i; } } }');
        checkTestEmitMainFunction("datatype Foo of F1 {} F2 {}; public function main(): Int { let x: Foo = F1{}; match(x) { F1 => { return 0i; } F2 => { return 1i; } } }", 'Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{MainᕒF1{}}; switch(x.uval.typeinfo->bsqtypeid) { case 26 /** Main::F1 **/: { MainᕒF1 ᑯx = x.uval.data.u_MainᕒF1; return 0_i; } default: { MainᕒF2 ᑯx = x.uval.data.u_MainᕒF2; return 1_i; } } }');
    });

    it("should emit binder match", function () {
        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); match(x) { None => { return 0i; } _ => { return 1i; } } }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; switch(x.typeinfo->bsqtypeid) { case 0 /** None **/: { None ᑯx = none; return 0_i; } default: { SomeᐸIntᐳ ᑯx = x.asSome(); return 1_i; } } }');
        checkTestEmitMainFunction("datatype Foo of F1 {} F2 { g: Int }; public function main(): Int { let x: Foo = F1{}; match(x) { F1 => { return 0i; } F2 => { return $x.g; } } }", 'Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{MainᕒF1{}}; switch(x.uval.typeinfo->bsqtypeid) { case 26 /** Main::F1 **/: { MainᕒF1 ᑯx = x.uval.data.u_MainᕒF1; return 0_i; } default: { MainᕒF2 ᑯx = x.uval.data.u_MainᕒF2; return ᑯx.g; } } }');

        checkTestEmitMainFunction("datatype Foo of F1 {} F2 { g: Int }; public function main(): Int { let x: Foo = F2{ 5i }; var r: Int; match(x) { F1 => { r = 0i; } F2 => { r = $x.g; } } return r; }", 'Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{MainᕒF2{5_i}}; Int r; switch(x.uval.typeinfo->bsqtypeid) { case 26 /** Main::F1 **/: { MainᕒF1 ᑯx = x.uval.data.u_MainᕒF1; r = 0_i; break; } default: { MainᕒF2 ᑯx = x.uval.data.u_MainᕒF2; r = ᑯx.g; break; } } return r; }');
    });
});

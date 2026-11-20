"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

const conceptcode_abstract = 'concept Bar { abstract method foo(): Int; }';
const conceptcode_virtual = 'concept Bar { virtual method foo(): Int { return 0i; } }';

const conceptcode_optabstract = 'concept Bar { abstract method foo(): Option<Int>; }';
const conceptcode_optvirtual = 'concept Bar { virtual method foo(): Option<Int> { return some(0i); } }';

describe ("CPPExec -- entity abstract/virtual methods", () => {
    it("should exec simple abstract/virtual (virtual calls) methods", function () {
        runTestSet(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} public function main(v: Foo): Int { return v.foo(); }`, [['Main::Foo{3i}', '3i']], []); 
        runTestSet(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } public function main(v: Foo): Int { return v.foo(); }`, [['Main::Foo{3i}', '0i']], []); 

        runTestSet(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} public function main(v: Bar): Int { return v.foo(); }`, [['Main::Foo{3i}', '3i']], []); 
        runTestSet(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } public function main(v: Bar): Int { return v.foo(); }`, [['Main::Foo{3i}', '0i']], []); 
    });

    it("should exec simple abstract/virtual (vary result) methods", function () {
        runTestSet(`${conceptcode_optabstract} entity Foo provides Bar { field f: Int; override method foo(): Some<Int> { return some(this.f); }} public function main(v: Bar): Int { return v.foo().@some; }`, [['Main::Foo{3i}', '3i']], []); 
        runTestSet(`${conceptcode_optvirtual} entity Foo provides Bar { field f: Int; } public function main(v: Bar): Int { return v.foo().@some; }`, [['Main::Foo{3i}', '0i']], []); 
    });

    it("should exec simple abstract/virtual (2 opts) methods", function () {
        runTestSet(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} entity Fizz provides Bar { override method foo(): Int { return 10i; }} public function main(v: Bar): Int { return v.foo(); }`, [['Main::Foo{3i}', '3i'], ['Main::Fizz{}', '10i']], []); 
        runTestSet(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } entity Fizz provides Bar { override method foo(): Int { return 10i; }} public function main(v: Bar): Int { return v.foo(); }`, [['Main::Foo{3i}', '0i'], ['Main::Fizz{}', '10i']], []); 
    });

    it("should emit simple abstract/virtual (requires/ensures) methods", function () {
        runTestSet(`concept Bar { abstract method foo(): Int ensures $return >= 0i; ; } entity Foo provides Bar { override method foo(): Int { return 1i; } } public function main(): Int { let v: Foo = Foo{}; let u: Bar = Foo{}; return v.foo() + u.foo(); }`, [[undefined, '2i']], []);  
        runTestSet(`concept Bar { virtual method foo(): Int ensures $return >= 0i; { return 5i; } } entity Foo provides Bar { } public function main(): Int { let v: Foo = Foo{}; let u: Bar = Foo{}; return v.foo() + u.foo(); }`, [[undefined, '10i']], []); 
    });
});

"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

const conceptcode_abstract = 'concept Bar { abstract method foo(): Int; }';
const conceptcode_virtual = 'concept Bar { virtual method foo(): Int { return 0i; } }';

const conceptcode_optabstract = 'concept Bar { abstract method foo(): Option<Int>; }';
const conceptcode_optvirtual = 'concept Bar { virtual method foo(): Option<Int> { return some(0i); } }';

describe ("Checker -- entity abstract/virtual methods", () => {
    it("should check simple abstract/virtual (virtual calls) methods", function () {
        checkTestFunction(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} function main(): Int { let v = Foo{3i}; return v.foo(); }`); 
        checkTestFunction(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } function main(): Int { let x = Foo{3i}; return x.foo(); }`); 

        checkTestFunction(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} function main(): Int { let v: Bar = Foo{3i}; return v.foo(); }`); 
        checkTestFunction(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } function main(): Int { let x: Bar = Foo{3i}; return x.foo(); }`); 
    });

    it("should check simple abstract/virtual (vary result) methods", function () {
        checkTestFunction(`${conceptcode_optabstract} entity Foo provides Bar { field f: Int; override method foo(): Some<Int> { return some(this.f); }} function main(): Int { let v: Bar = Foo{3i}; return v.foo().@some; }`); 
        checkTestFunction(`${conceptcode_optvirtual} entity Foo provides Bar { field f: Int; } function main(): Int { let x: Bar = Foo{3i}; return x.foo().@some; }`); 
    });

    it("should check simple abstract/virtual (2 opts) methods", function () {
        checkTestFunction(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} entity Fizz provides Bar { override method foo(): Int { return 10i; }} function main(): Int { let v: Bar = Foo{3i}; return v.foo(); }`); 
        checkTestFunction(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } entity Fizz provides Bar { override method foo(): Int { return 10i; }} function main(): Int { let x: Bar = Foo{3i}; return x.foo(); }`); 
    });
});

"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

const conceptcode_abstract = 'concept Bar { abstract method foo(): Int; }';
const conceptcode_virtual = 'concept Bar { virtual method foo(): Int { return 0i; } }';

const conceptcode_optabstract = 'concept Bar { abstract method foo(): Option<Int>; }';
const conceptcode_optvirtual = 'concept Bar { virtual method foo(): Option<Int> { return some(0i); } }';

describe ("Parser -- entity abstract/virtual methods", () => {
    it("should parse simple abstract/virtual (virtual calls) methods", function () {
        parseTestFunctionInFile(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} [FUNC]`, 'function main(): Int { let v = Foo{3i}; return v.foo(); }'); 
        parseTestFunctionInFile(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } [FUNC]`, 'function main(): Int { let x = Foo{3i}; return x.foo(); }'); 

        parseTestFunctionInFile(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} [FUNC]`, 'function main(): Int { let v: Bar = Foo{3i}; return v.foo(); }'); 
        parseTestFunctionInFile(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } [FUNC]`, 'function main(): Int { let x: Bar = Foo{3i}; return x.foo(); }'); 
    });

    it("should parse simple abstract/virtual (vary result) methods", function () {
        parseTestFunctionInFile(`${conceptcode_optabstract} entity Foo provides Bar { field f: Int; override method foo(): Some<Int> { return some(this.f); }} [FUNC]`, 'function main(): Int { let v: Bar = Foo{3i}; return v.foo().@some; }'); 
        parseTestFunctionInFile(`${conceptcode_optvirtual} entity Foo provides Bar { field f: Int; } [FUNC]`, 'function main(): Int { let x: Bar = Foo{3i}; return x.foo().@some; }'); 
    });

    it("should parse simple abstract/virtual (2 opts) methods", function () {
        parseTestFunctionInFile(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} entity Fizz provides Bar { override method foo(): Int { return 10i; }} [FUNC]`, 'function main(): Int { let v: Bar = Foo{3i}; return v.foo(); }'); 
        parseTestFunctionInFile(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } entity Fizz provides Bar { override method foo(): Int { return 10i; }} [FUNC]`, 'function main(): Int { let x: Bar = Foo{3i}; return x.foo(); }'); 
    });
});

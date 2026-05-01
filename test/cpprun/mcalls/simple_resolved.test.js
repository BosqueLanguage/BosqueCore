"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- entity methods", () => {
    it("should exec simple entity methods", function () {
        runTestSet('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(y: Int): Int { return Foo{y}.foo(); }', [['3i', '3i']], []);
        runTestSet('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', [['3i', '4i']], []);
    });

    it("should exec simple entity methods multiple options", function () {
        runTestSet('entity Foo { field f: Int; method foo(): Int { return this.f; } method foo(out x: Int): Int { x = 3i; return x; } } public function main(z: Int): Int { let x = Foo{z}; var y: Int; let tt = x.foo(out y); return y + tt; }', [['3i', '6i']], []);
        runTestSet('entity Foo { field f: Int; method foo(): Int { return this.f; } method foo(f: fn() -> Int): Int { return f() + this.foo(); } } public function main(z: Int): Int { let x = Foo{z}; return x.foo(fn() => 3i); }', [['3i', '6i'], ['4i', '7i']], []);
    });
});

describe ("CPPExec -- eADT methods", () => {
    it("should exec simple eADT methods with template", function () {
        runTestSet('datatype Foo of Foo1 { field f: Int; method foo<T>(): Bool { return this.f.?<T>; }} ; public function main(y: Int): Bool { let x = Foo1{y}; return x.foo<Int>(); }', [['0i', 'true']], []); 
    
        runTestSet('datatype Foo of F1 { f: Int } F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1{3i}.foo(); }', [['3i', '3i']], []); 
    });

    it("should emit template ROOT eADT methods", function () {
        runTestSet('datatype Foo<T> of F1 { f: T } F2 { g: T } & { method foo(): T { if(this)@<F1<T>> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1<Int>{3i}.foo(); }', [['3i', '3i']], []); 
    });
});

describe ("CPPExec -- type alias methods", () => {
    it("should exec simple type alias methods", function () {
        runTestSet('type Foo = Int & { method foo(x: Int): Int { return this.value + x; }} public function main(): Int { return 3i<Foo>.foo(1i); }', [['3i', '4i']], []); 
        runTestSet('type Foo = Int & { method foo<T>(): Bool { return this.value.?<T>; }} public function main(): Bool { let x = 3i<Foo>; return x.foo<Nat>(); }', [['3i', 'false']], []); 
    });
});

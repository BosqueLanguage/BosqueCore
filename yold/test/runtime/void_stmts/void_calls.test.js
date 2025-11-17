"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Void NamespaceFunction Ref Params", () => {
    it("should check simple ref", function () {
        runMainCode('entity Foo{ field g: Bool; } function foo(ref y: Foo) { ref y[g = true]; return; } public function main(): Bool { var ff = Foo{false}; foo(ref ff); return ff.g; }', "true");    
    });
});

describe ("Exec -- Void method Ref Params", () => {
    it("should check simple ref", function () {
        runMainCode('entity Foo{ field g: Bool; ref method foo() { ref this[g = true]; return; } } public function main(): Bool { var ff = Foo{false}; ref ff.foo(); return ff.g; }', "true");    
    });
});


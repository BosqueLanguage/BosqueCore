"use strict";

import { runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const dtype = 'concept Bar { field k: Int = 3i; field j: Int = $k + 5i; abstract method foo(): Int; } entity Foo provides Bar { override method foo(): Int { return this.k; } } public function main(x: Int): Int { let v: Foo = Foo{}; let u: Bar = Foo{x}; return v.foo() + u.foo(); }';

describe ("vcall and defaults exec", () => {
    it("vcall and defaults should succeed", function () {
        runTestSet(`${dtype}`, [['1i', '4i']], []);
    });
});

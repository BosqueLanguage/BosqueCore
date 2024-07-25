"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- access argument", () => {
    it("should check simple arg var access", function () {
        checkTestFunction("entity Foo { field f: Int; } function main(x: Foo): Int { return x.f; }");
        checkTestFunction("entity Foo { field f: Int; } function foo(): Foo { return Foo{1i}; } function main(): Int { return foo().f; }");

        checkTestFunction("entity Foo { field f: Int; field g: Nat; } function main(x: Foo): Nat { return x.g; }");
        checkTestFunction("entity Bar { field h: Bool; } entity Foo { field f: Bar; } function main(x: Foo): Bool { return x.f.h; }");
    });

    it("should fail simple wrong type", function () {
        checkTestFunctionError("entity Foo { field f: Int; } function main(x: Foo): Bool { return x.f; }", "Expected a return value of type Bool but got Int");
        checkTestFunctionError("entity Foo { field f: Int; } function main(x: Foo): Bool { return x.g; }", "Could not find field g in type Foo");
    });
});

"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- access enum", () => {
    it("should check simple enum access", function () {
        checkTestFunction("enum Foo {f, g} function main(): Foo { return Foo#f; }");
    });

    it("should fail simple enum issues", function () {
        checkTestFunctionError("enum Foo {f, g} function main(): Foo { return Foo#h; }", "Enum Foo does not have member h");
        checkTestFunctionError("enum Foo {f, g} function main(): Int { return Foo#f; }", "Expected a return value of type Int but got Foo");
    });
});

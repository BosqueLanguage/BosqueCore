"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- access argument", () => {
    it("should parse simple arg var access", function () {
        parseTestFunction("function main(x: Int): Int { return x; }", undefined);
        parseTestFunction("function main(x: Int, y: Bool): Bool { return y; }", undefined);
    });

    it("should fail undefined name", function () {
        parseTestFunctionError("function main(x: Int): Int { return y; }", "Could not resolve 'y' in this context");
    });

    it("should fail _ arg", function () {
        parseTestFunctionError("function main(_: Int): Int { return 1i; }", 'Expected "[IDENTIFIER]" but got "_" when parsing "function parameter"');
    });

    it("should fail _ name", function () {
        parseTestFunctionError("function main(x: Int): Int { return _; }", "Unexpected token in expression -- _");
    });
});



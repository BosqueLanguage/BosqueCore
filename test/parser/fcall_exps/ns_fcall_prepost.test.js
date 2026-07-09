import { parseTestFunctionInFile, parseTestFunctionInFileError, parseTestFunctionInFilePlus, parseTestFunctionInFilePlusError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- NamespaceFunction Pre/Post", () => {
    it("should parse pre/post", function () {
        parseTestFunctionInFile('function foo(x: Int): Int requires x > 0i; { return 1i; } [FUNC]', 'function main(): Int { return foo(1i); }');
        parseTestFunctionInFile('function foo(x: Int): Int requires x > 0i; requires x > 1i; { return 1i; } [FUNC]', 'function main(): Int { return foo(1i); }');

        parseTestFunctionInFile('function foo(x: Int): Int ensures $return > 0i; { return 1i; } [FUNC]', 'function main(): Int { return foo(1i); }');
        parseTestFunctionInFile('function foo(x: Int): Int ensures $return > 0i; ensures $return > 1i; { return 1i; } [FUNC]', 'function main(): Int { return foo(1i); }');

        parseTestFunctionInFile('function foo(x: Int): Int requires x > 0i; ensures $return > 0i; { return 1i; } [FUNC]', 'function main(): Int { return foo(1i); }');  
    });

    it("should parse (fail) pre/post", function () {
        parseTestFunctionInFileError('function foo(x: Int): Int requires x > 0i { return 1i; }', 'Expected ";" but got "{" when parsing "requires"');
        parseTestFunctionInFileError('function foo(x: Int): Int ensures $return > 0i { return 1i; }', 'Expected ";" but got "{" when parsing "ensures"');
        parseTestFunctionInFileError('function foo(x: Int): Int ensures $return > 0i; requires x > 0i; { return 1i; }', 'Unexpected token in expression -- requires');  
    });
});

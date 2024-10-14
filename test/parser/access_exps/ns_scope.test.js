import { parseTestFunctionInFile, parseTestFunctionInFilePlus, parseTestFunctionInFilePlusError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

const ctxcode = [
    'declare namespace NSOther; entity Foo { }'
];

describe ("Parser -- access argument", () => {
    it("should parse implicit access", function () {
        parseTestFunctionInFilePlus("declare namespace Main; [FUNC]", 'function main(x: Int): Int { return x; }', undefined, ...ctxcode);  //Core is always ok
        parseTestFunctionInFilePlus("declare namespace Main; entity Bar { } [FUNC]", 'function main(): Option<Bar> { return none; }', 'function main(): Option<Bar> { return none; }', ...ctxcode);  //Implicit same namespace is ok
        parseTestFunctionInFilePlus("declare namespace Main; entity Bar { } [FUNC]", 'function main(): Option<Main::Bar> { return none; }', undefined, ...ctxcode);  //Explicit same namespace is ok
    });

    it("should parse imported access", function () {
        parseTestFunctionInFilePlus("declare namespace Main { using NSOther; } [FUNC]", 'function main(): Option<NSOther::Foo> { return none; }', undefined, ...ctxcode);  //Import no rename
        parseTestFunctionInFilePlus("declare namespace Main { using NSOther as Other; } [FUNC]", 'function main(): Option<Other::Foo> { return none; }', undefined, ...ctxcode);  //Import with rename
    });

    it("should fail undefined namespace", function () {
        parseTestFunctionInFilePlusError('declare namespace Main; function main(): Option<Other::Foo> { return none; }', "Unknown namespace Other", ...ctxcode);  //NS does not exist
    });

    it("should fail not-imported namespace", function () {
        parseTestFunctionInFilePlusError('declare namespace Main; function main(): Option<NSOther::Foo> { return none; }', "Missing import for namespace NSOther", ...ctxcode);  //NS exists but not imported
    });
});

describe ("Parser -- access nested namespace functions", () => {
    it("should parse top to nested", function () {
        parseTestFunctionInFile("namespace NSX { function foo(): Int { return 3i; } } [FUNC]", 'function main(x: Int): Int { return NSX::foo(); }');
        parseTestFunctionInFile("namespace NSX { function foo(): Int { return 3i; } } [FUNC]", 'function main(x: Int): Int { return NSX::foo(); }');
    });

    it("should parse nested cross", function () {
        parseTestFunctionInFile("namespace NSX { function bar(): Int { return NSX::foo(); } function foo(): Int { return 3i; } } [FUNC]", 'function main(x: Int): Int { return NSX::bar(); }');
        parseTestFunctionInFile("namespace NSX { function bar(): Int { return foo(); } function foo(): Int { return 3i; } } [FUNC]", 'function main(x: Int): Int { return NSX::bar(); }');
    });

    it("should parse nested up", function () {
        parseTestFunctionInFile("function foo(): Int { return 3i; } namespace NSX { function bar(): Int { return foo(); } } [FUNC]", 'function main(x: Int): Int { return NSX::bar(); }');

        parseTestFunctionInFile("function foo(): Int { return 3i; } namespace NSX { function bar(): Int { return foo(); } } [FUNC]", 'function main(x: Int): Int { return NSX::bar(); }');
    });

    it("should parse nested internal first", function () {
        parseTestFunctionInFile("function foo(): Int { return 3i; } namespace NSX { function foo(): Int { return 0i; } function bar(): Int { return foo(); } } [FUNC]", 'function main(x: Int): Int { return NSX::bar(); }');
        parseTestFunctionInFile("function foo(): Nat { return 3n; } namespace NSX { function foo(): Int { return 3i; } function bar(): Int { return foo(); } } [FUNC]", 'function main(x: Int): Int { return NSX::bar(); }');
    });
});

"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- ref updates", () => {
    it("should check ref updates direct", function () {
        checkTestFunctionInFile('entity Foo { field x: Int; } public function main(x: Int): Int { var z = Foo{x}; ref z[x = 5i]; return z.x; }');
        checkTestFunctionInFile('entity Foo { field x: Int; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = 5i]; return z.x; }');

        checkTestFunctionInFile('entity Foo { field x: Int; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = $x + 1i]; return z.x; }');

        checkTestFunctionInFile('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[x = 5i]; return z.x; }');
        checkTestFunctionInFile('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[y = true, x = 9i]; return z.x; }');
    });

    it("should check ref updates as params", function () {
        checkTestFunctionInFile('entity Foo { field x: Int; } public function main(ref z: Foo): Int { ref z[x = 5i]; return z.x; }');
        checkTestFunctionInFile('entity Foo { field x: Int; ref method f() { ref this[x = 0i]; return; } } public function main(): Int { ref z = Foo{3i}; ref z.f(); return z.x; }');

        //don't need return value for Void invokes
        checkTestFunctionInFile('entity Foo { field x: Int; ref method f() { ref this[x = 0i]; } } public function main(): Int { ref z = Foo{3i}; ref z.f(); return z.x; }');
    });

    it("should fail ref updates", function () {
        checkTestFunctionInFileError('entity Foo { field x: Int; } public function main(x: Int): Int { var z = 5i; ref z[q = 3i]; return z.x; }', 'Variable z is not an updatable type (entity/concept or datatype)');

        checkTestFunctionInFileError('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[y = $x != 0i]; return z.x; }', "Variable $x is not declared here");

        checkTestFunctionInFileError('entity Foo { field x: Int; } public function main(x: Int): Int { var z = Foo{x}; ref z[q = 3i]; return z.x; }', 'Field q is not a member of type Foo');
        checkTestFunctionInFileError('entity Foo { field x: Int; } public function main(x: Int): Int { let z = Foo{x}; ref z[x = 0i]; return z.x; }', 'Variable z is cannot be updated (is local const or not a ref param)');
    });
});

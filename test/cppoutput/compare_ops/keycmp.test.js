"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- basic KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("public function main(): Bool { return KeyComparator::equal<Nat>(0n, 1n); }", "false");
        runMainCode("public function main(): Bool { return KeyComparator::equal<Nat>(1n, 1n); }", "true");

        runMainCode("public function main(): Bool { return KeyComparator::less<Nat>(0n, 1n); }", "true");
        runMainCode("public function main(): Bool { return KeyComparator::less<Nat>(1n, 1n); }", "false");

        runMainCode("public function main(): Bool { return KeyComparator::equal<CString>('', 'ok'); }", "false");
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('', 'ok'); }", "true");
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('ok', 'ok'); }", "false");

        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('oj', 'ok'); }", "true");
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('on', 'ok'); }", "false");

        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('abcdefghijka', 'abcdefghijkb'); }", "true");
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('abcdefghijka', 'abcdefghijkb'); }", "true");
    });
});

describe ("CPP Emit Evaluate -- large-ish cstring(rope) KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('abcdefghijka', 'abcdefghijkb'); }", "true");
        runMainCode("public function main(): Bool { return KeyComparator::equal<CString>('abcdefghijka', 'abcdefghijka'); }", "true");

        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('Hello, World!', 'hello, world!'); }", "true");
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('Hello, World!', 'hello, world!'); }", "true");

        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('Lorem ipsum dolor sit amet', 'Lorem ipsum dolor sit amet, consectetur adipiscing elit'); }", "true");
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('Lorem ipsum dolor sit amet', 'Lorem ipsum dolor sit amet'); }", "false");
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('Lorem ipsum dolor sit amet, consectetur adipiscing elit', 'Lorem ipsum dolor sit amet'); }", "false");
    });
});

// TODO: Not supported!
/*
describe ("CPP Emit Evaluate -- type alias KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::equal<Foo>(1i<Foo>, 1i<Foo>); }", "true");
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::equal<Foo>(0i<Foo>, 1i<Foo>); }", "false");

        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(0i<Foo>, 1i<Foo>); }", "true");
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(1i<Foo>, 1i<Foo>); }", "false");
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(2i<Foo>, 1i<Foo>); }", "false");
    });
});
*/

describe ("CPP Emit Evaluate -- enum KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, Foo#f); }", "true");
        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, Foo#g); }", "false");

        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::less<Foo>(Foo#f, Foo#f); }", "false");
        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::less<Foo>(Foo#f, Foo#g); }", "true");
    });
});

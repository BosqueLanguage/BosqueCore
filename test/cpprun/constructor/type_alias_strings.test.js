"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPexec-- String Type Alias Constructor", () => {
    it("should exec simple type alias", function () {
        runTestSet("type Foo = CString; public function main(x: Int): Foo { return 'ok'<Foo>; }", [['0i', "'ok'<Main::Foo>"]], []);
        runTestSet("type Foo = CString; public function main(x: CString): Foo { return Foo{x}; }", [['"one"', "'one'<Main::Foo>"], ['"two"', "'two'<Main::Foo>"]], []);
    });
});

describe ("CPPexec-- Type Alias w/ Invariant Constructor", () => {
    it("should exec type alias with invariant", function () {
        runTestSet("type Foo = CString{3n, } of /[0-9]+/c; public function main(x: Int): Foo { return '345'<Foo>; }", [['0i', "'345'<Main::Foo>"]], []);

        runTestSet("const re2: CRegex = /[0-9]+/c; type Foo = CString{3n, } of Main::re2; public function main(x: Int): Foo { return '345'<Foo>; }", [['0i', "'345'<Main::Foo>"]], []);
        runTestSet("const re2: CRegex = /[0-9]+/c; type Foo = CString{, 2n} of Main::re2; public function main(x: Int): Foo { return '3'<Foo>; }", [['0i', "'3'<Main::Foo>"]], []);

        runTestSet("const re2: CRegex = /[0-9]+/c; type Foo = CString{3n, } of Main::re2; public function main(x: CString): Foo { return Foo{x}; }", [['"345"', "'345'<Main::Foo>"]], ['"aaaa"', '"0"']);
        runTestSet("const re2: CRegex = /[0-9]+/c; type Foo = CString{, 2n} of Main::re2; public function main(x: CString): Foo { return Foo{x}; }", [['"3"', "'3'<Main::Foo>"]], ['"a"', '"000"']);
    });
});

describe ("CPPExec -- type decl zipcode/css", () => {
    it("should exec string options type decl", function () {
        runTestSet("type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c; public function main(x: Int): Zipcode { return '98052-0000'<Zipcode>; }", [['0i', "'98052-0000'<Main::Zipcode>"]], []);
        runTestSet("type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c; public function main(x: Int): Zipcode { return '40502'<Zipcode>; }", [['0i', "'40502'<Main::Zipcode>"]], []);
        runTestSet("type CSSPt = CString of /[0-9]+'pt'/c; public function main(x: Int): CSSPt { return '3pt'<CSSPt>; }", [['0i', "'3pt'<Main::CSSPt>"]], []);

        runTestSet("type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c; public function main(x: CString): Zipcode { return Zipcode{x}; }", [['"40502"', "'40502'<Main::Zipcode>"]], ['"A111"']);
        runTestSet("type CSSPt = CString of /[0-9]+'pt'/c; public function main(x: CString): CSSPt { return CSSPt{x}; }", [['"3pt"', "'3pt'<Main::CSSPt>"]], ['"3px"']);
    });
});

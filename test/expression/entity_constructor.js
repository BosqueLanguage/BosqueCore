"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Foo constructor', function () {
    const testopt = ["expression/entity_constructor", "foo"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Foo{3i}', function () {
        it('expected Foo{3i}', function () {
            expect(invokeExecutionOn(jsmain)).to.eql({f:3});
        });
    });
});

describe('baz constructor', function () {
    const testopt = ["expression/entity_constructor", "baz"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Baz{3i, 4n}', function () {
        it('expected Baz{3i, 4n}', function () {
            expect(invokeExecutionOn(jsmain)).to.eql({g:3, h:4});
        });
    });
});

describe('qux constructor', function () {
    const testopt = ["expression/entity_constructor", "qux"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Qux{"bob", 3i}', function () {
        it('expected Qux{"bob", 3i}', function () {
            expect(invokeExecutionOn(jsmain)).to.eql({g:3, name:"bob"});
        });
    });
});

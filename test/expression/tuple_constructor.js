"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Empty tuple', function () {
    const testopt = ["expression/tuple_constructor", "tuple_empty"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('[]', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("[]");
        });
    });
});

describe('Three tuple', function () {
    const testopt = ["expression/tuple_constructor", "tuple_3int"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('[1, 2, 3]', function () {
        it('expected [i1, 2i, 3i]', function () {
            expect(invokeExecutionOn(jsmain, "2i")).to.eql("[1i, 2i, 3i]");
        });
    });
    describe('[1, -1, 3]', function () {
        it('expected [i1, -1i, 3i]', function () {
            expect(invokeExecutionOn(jsmain, "-1i")).to.eql("[1i, -1i, 3i]");
        });
    });
});

describe('Nested tuple', function () {
    const testopt = ["expression/tuple_constructor", "tuple_nested"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('[1, [true]]', function () {
        it('expected [i1, [true]]', function () {
            expect(invokeExecutionOn(jsmain, "1i")).to.eql("[1i, [true]]");
        });
    });
    describe('[-1, [true]]', function () {
        it('expected [-1i, [true]]', function () {
            expect(invokeExecutionOn(jsmain, "-1i")).to.eql("[-1i, [true]]");
        });
    });
});


describe('Infer tuple', function () {
    const testopt = ["expression/tuple_constructor", "tuple_infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(0)', function () {
        it('expected [0, none]', function () {
            expect(invokeExecutionOn(jsmain, "0i")).to.eql("[0i, none]");
        });
    });
    describe('process(5)', function () {
        it('expected [5, true]', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("[5i, true]");
        });
    });
});


"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('ITest convert type concept', function () {
    const testopt = ["expression/itest_conversion", "convert_named"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Qux@ITest', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(2);
        });
    });
    describe('Qux@ITest (fail)', function () {
        it('expected failure', function () {
            expect(invokeExecutionOn(jsmain, false)).to.include("error -- cannot convert value");
        });
    });
});


describe('ITest convert type union', function () {
    const testopt = ["expression/itest_conversion", "convert_union"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Qux@ITest', function () {
        it('expected [1i, 1i, 1i]', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql([1, 1, 1]);
        });
    });
    describe('Qux@ITest (fail)', function () {
        it('expected failure', function () {
            expect(invokeExecutionOn(jsmain, false)).to.include("error -- cannot convert value");
        });
    });
});


describe('ITest convert result ok', function () {
    const testopt = ["expression/itest_conversion", "convert_result_ok"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITest result ok', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain)).to.eql(3);
        });
    });
});


describe('ITest convert result error', function () {
    const testopt = ["expression/itest_conversion", "convert_result_err"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITest result err', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain)).to.eql(false);
        });
    });
});

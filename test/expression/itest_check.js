"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('ITest check type concept', function () {
    const testopt = ["expression/itest_check", "check_named"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Qux?ITest', function () {
        it('expected [true, false]', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql([true, false]);
        });
    });
    describe('Qux?!ITest', function () {
        it('expected [false, true]', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql([false, true]);
        });
    });
});

describe('ITest check type union', function () {
    const testopt = ["expression/itest_check", "check_union"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Qux ITest', function () {
        it('expected [true, false, false, true, true]', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql([true, false, false, true, true]);
        });
    });
    describe('None ITest', function () {
        it('expected [false, true, true, false, false]', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql([false, true, true, false, false]);
        });
    });
});

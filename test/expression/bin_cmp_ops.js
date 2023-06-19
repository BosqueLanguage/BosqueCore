"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Equality', function () {
    const testopt = ["expression/bin_cmp_ops", "eqops"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('eqop 1i, -3.0f, 1/3R, 1I_Foo', function () {
        it('expected [true, true, false, true, false]', function () {
            expect(invokeExecutionOn(jsmain, "1i", "-3.0f", "1/3R", "1I_Foo")).to.eql("[true, true, false, true, false]");
        });
    });
    describe('eqop 2i, 1.0f, 5/2R, 3I_Foo', function () {
        it('expected [false, false, true, false, true]', function () {
            expect(invokeExecutionOn(jsmain, "2i", "1.0f", "5/2R", "3I_Foo")).to.eql("[false, false, true, false, true]");
        });
    });
});

describe('Less', function () {
    const testopt = ["expression/bin_cmp_ops", "ltops"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ltop 2, -3.0, 3/2, 1', function () {
        it('expected [false, true, true, false, true]', function () {
            expect(invokeExecutionOn(jsmain, 2, -3.0, "3/2", 1)).to.eql([false, true, true, false, true]);
        });
    });
    describe('ltop 0, 0.0, 1/6, 2', function () {
        it('expected [true, true, false, true, false]', function () {
            expect(invokeExecutionOn(jsmain, 0, 0.0, "1/6", 2)).to.eql([true, true, false, true, false]);
        });
    });
});

describe('Greater', function () {
    const testopt = ["expression/bin_cmp_ops", "gtops"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

   
    describe('gtop 2, -3.0, 3/2, 1', function () {
        it('expected [true, true, true, true, true]', function () {
            expect(invokeExecutionOn(jsmain, 2, -3.0, "3/2", 1)).to.eql([true, true, true, true, true]);
        });
    });
    describe('gtop 0, 0.0, 1/6, 2', function () {
        it('expected [false, false, true, false, true]', function () {
            expect(invokeExecutionOn(jsmain, 0, 0.0, "1/6", 2)).to.eql([false, false, true, false, true]);
        });
    });
});

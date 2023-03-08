"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Eq Basics', function () {
    const testopt = ["expression/strong_equality", "eq_basics"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('checks', function () {
        it('expected [true, true, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([true, true, false]);
        });
    });
});

describe('Eq Int|None', function () {
    const testopt = ["expression/strong_equality", "int_none"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('checks', function () {
        it('expected [false, true, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([false, true, false]);
        });
    });
});

describe('Eq Option', function () {
    const testopt = ["expression/strong_equality", "option"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('checks', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain)).to.eql(false);
        });
    });
});

describe('Eq Mixed Key', function () {
    const testopt = ["expression/strong_equality", "mixed_key"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('checks hello', function () {
        it('expected [true, false]', function () {
            expect(invokeExecutionOn(jsmain, "hello")).to.eql([true, false]);
        });
    });
    describe('checks goodbye', function () {
        it('expected [false, true]', function () {
            expect(invokeExecutionOn(jsmain, "goodbye")).to.eql([false, true]);
        });
    });
    describe('checks none', function () {
        it('expected [false, true]', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql([false, true]);
        });
    });
});

describe('Eq entity none', function () {
    const testopt = ["expression/strong_equality", "entity_none"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('checks', function () {
        it('expected [false, true, true, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([false, true, true, false]);
        });
    });
});

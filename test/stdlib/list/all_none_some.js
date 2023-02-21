"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List All/Some/None basic', function () {
    const testopt = ["stdlib/list/all_none_some", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected [false, true, false]', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.eql([false, true, false]);
        });
    });
    describe('List{0, 2, 0}', function () {
        it('expected [false, false, true]', function () {
            expect(invokeExecutionOn(jsmain, [0, 2, 0])).to.eql([false, false, true]);
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected [true, true, false]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([true, false, true]);
        });
    });
});

describe('List All/Some/None empty', function () {
    const testopt = ["stdlib/list/all_none_some", "empty"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected [true, true, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([true, true, false]);
        });
    });
});

describe('List All/Some/None index basic', function () {
    const testopt = ["stdlib/list/all_none_some", "idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected [true, false, true]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([true, false, true]);
        });
    });
    describe('List{3, 2, 1}', function () {
        it('expected [false, false, true]', function () {
            expect(invokeExecutionOn(jsmain, [3, 2, 1])).to.eql([false, false, true]);
        });
    });
    describe('List{9, 9, 9}', function () {
        it('expected [false, true, false]', function () {
            expect(invokeExecutionOn(jsmain, [9, 9, 9])).to.eql([false, true, false]);
        });
    });
});

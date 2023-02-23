"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List zip basic', function () {
    const testopt = ["stdlib/list/zip_ops", "zip_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected [2, 3, 4]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([[1, "one"], [2, "two"], [3, "three"]]);
        });
    });
    describe('List{1, 2}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [1, 2])).to.includes("Failed precondition");
        });
    });
});

describe('List zipwith basic', function () {
    const testopt = ["stdlib/list/zip_ops", "zipwith_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected [1, 3, 5]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([true, false, true]);
        });
    });
    describe('List{1, 2}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [1, 2])).to.includes("Failed precondition");
        });
    });
});

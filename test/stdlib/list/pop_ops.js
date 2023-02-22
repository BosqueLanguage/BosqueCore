"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List popBack basic', function () {
    const testopt = ["stdlib/list/pop_ops", "pop_back"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [])).to.includes("Failed precondition");
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected List{1, 2}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([1, 2]);
        });
    });
});

describe('List popFront basic', function () {
    const testopt = ["stdlib/list/pop_ops", "pop_front"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [])).to.includes("Failed precondition");
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected List{2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([2, 3]);
        });
    });
});

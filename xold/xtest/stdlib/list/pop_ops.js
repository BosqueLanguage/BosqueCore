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
            expect(invokeExecutionOn(jsmain, "List{}")).to.includes("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}', function () {
        it('expected List{1i, 2i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{1i, 2i}");
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
            expect(invokeExecutionOn(jsmain, "List{}")).to.includes("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}', function () {
        it('expected List{2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{2i, 3i}");
        });
    });
});

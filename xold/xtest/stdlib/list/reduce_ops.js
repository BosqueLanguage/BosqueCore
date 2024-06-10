"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List reduce basic', function () {
    const testopt = ["stdlib/list/reduce_ops", "reduce_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected 6i', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("6i");
        });
    });
    describe('List{}', function () {
        it('expected 0i', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("0i");
        });
    });
});

describe('List reduce idx basic', function () {
    const testopt = ["stdlib/list/reduce_ops", "reduce_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected 9i', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("9i");
        });
    });
    describe('List{}', function () {
        it('expected 0i', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("0i");
        });
    });
});

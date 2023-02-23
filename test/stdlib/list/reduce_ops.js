"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List reduce basic', function () {
    const testopt = ["stdlib/list/reduce_ops", "reduce_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected 6', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql(6);
        });
    });
    describe('List{}', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql(0);
        });
    });
});

describe('List reduce idx basic', function () {
    const testopt = ["stdlib/list/reduce_ops", "reduce_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected 9', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql(9);
        });
    });
    describe('List{}', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql(0);
        });
    });
});

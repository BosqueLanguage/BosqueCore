"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List find basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.includes("Assertion failed");
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected 2', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql(2);
        });
    });
});

describe('List findIndexOf basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_index_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.includes("Assertion failed");
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql(1);
        });
    });
});

describe('List findIdx basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.includes("Assertion failed");
        });
    });
    describe('List{0, -2, 0}', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, [0, -2, 0])).to.eql(-2);
        });
    });
});

describe('List findIndexOfIdx basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_index_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.includes("Assertion failed");
        });
    });
    describe('List{0, -2, 0}', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, [0, -2, 0])).to.eql(1);
        });
    });
});

"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List find basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0i, 0i, 0i}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, 0i, 0i}")).to.includes("Assertion failed");
        });
    });
    describe('List{1i, 2i, 3i}', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("2i");
        });
    });
});

describe('List findIndexOf basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_index_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0i, 0i, 0i}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, 0i, 0i}")).to.includes("Assertion failed");
        });
    });
    describe('List{1i, 2i, 3i}', function () {
        it('expected 1n', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("1n");
        });
    });
});

describe('List findIdx basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0i, 0i, 0i}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, 0i, 0i}")).to.includes("Assertion failed");
        });
    });
    describe('List{0i, -2i, 0i}', function () {
        it('expected 1n', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, -2i, 0i}")).to.eql("-2i");
        });
    });
});

describe('List findIndexOfIdx basic', function () {
    const testopt = ["stdlib/list/find_ops", "find_index_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0i, 0i, 0i}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, 0i, 0i}")).to.includes("Assertion failed");
        });
    });
    describe('List{0i, -2i, 0i}', function () {
        it('expected 1n', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, -2i, 0i}")).to.eql("1n");
        });
    });
});
